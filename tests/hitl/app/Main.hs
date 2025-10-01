{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PackageImports #-}
{-# OPTIONS_GHC -Wno-deprecations #-}

import Prelude

import Control.Concurrent.QSem (QSem, newQSem, waitQSem, signalQSem)
import Control.Exception
  ( SomeException, Exception, Handler(..)
  , catches, throw, bracket_
  )
import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)
import Data.ByteString
  ( ByteString
  , append, hGet, hGetNonBlocking, hPut, pack, unpack, singleton
  )
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy(..))
import Data.Typeable (Typeable, typeRep)
import Data.Word (Word8)
import GHC.IO.Handle (Handle)
import Hedgehog (PropertyT, (===), property, forAll)
import System.Exit (ExitCode, exitWith)
import System.Environment (setEnv, withArgs)
import System.Hardware.Serialport
  ( SerialPortSettings(..), CommSpeed(..)
  , defaultSerialSettings, hWithSerial
  )
import System.IO (BufferMode(..), hSetBuffering)
import Test.Tasty
  ( TestTree, DependencyType(..)
  , defaultMain, localOption, sequentialTestGroup, testGroup, withResource
  )
import Test.Tasty.Hedgehog (HedgehogTestLimit(..), testProperty)
import Text.Printf (printf)
import Text.Read (readMaybe)

import qualified Data.ByteString as BS
  (concatMap, empty, null, uncons, unsnoc, pack, length, replicate)
import qualified Data.Modular    as Modular
import qualified System.Timeout  as TO (timeout)
import qualified Hedgehog.Gen    as Gen (bytes, integral)
import qualified Hedgehog.Range  as Range (linear, constantFrom)

import qualified Crypto.Hash.SHA1    as SHA1 (hash)
import qualified Crypto.Hash.SHA224  as SHA224 (hash)
import qualified Crypto.Hash.SHA256  as SHA256 (hash)
import qualified Crypto.Hash.SHA384  as SHA384 (hash)
import qualified Crypto.Hash.SHA512  as SHA512 (hash)
import qualified Crypto.Hash.SHA512t as SHA512t (hash)
import qualified "cryptohash" Crypto.MAC.HMAC     as HMAC (hmac)

import qualified Clash.Crypto.Cipher.AES.Specification as SpecAES
import Crypto.Cipher.AES as Reference (AES128, AES192, AES256) 
import Crypto.Cipher.Types
import Crypto.Error

import Clash.Prelude
  ( type Div, type (*), Nat, KnownNat, Unsigned, Vec
  , toList, resize,  bitCoerce, natToNum
  )
import Clash.Crypto.Hash.SHA
  ( SHA(..), MessageDigestSize, KnownSHA(..), SHAFacts(..), BlockSize
  )
import Clash.Crypto.Cipher.AES
  ( AES(..), AESKeyExpansion(..), KnownAESStream(..), KnownAES(..), AESStreamFacts(..),
   AESFacts(..), InType, OutType, KeyType, Nb,Nk,Nr,aesECBencryption, aesECBdecryption
  )
import Clash.Crypto.Hitlt.Shared (Q, isReadyIndicator)
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)

import Shake
  ( ShakeOptions(..), Verbosity(..)
  , shakeOptions, shakeBuild, configLookup
  )

main ∷ IO ()
main = do
  lkup ← configLookup

  let serialDev = lkup "HITLT_SERIAL_DEV"
      serialSpeed = lkup "SERIAL_SPEED"
      settings = defaultSerialSettings { commSpeed = parseCS serialSpeed }

  -- using only a single serial forces us to use single threaded test
  -- executation at this points
  setEnv "TASTY_NUM_THREADS" "1"

  sem ← newQSem 1

  run sem serialDev settings `catches`
    [ Handler $ \(e ∷ ExitCode) → exitWith e
    , Handler $ \(e ∷ SomeException) → error $ show e
    ]
 where
  run sem dev settings
    = defaultMain $ testGroup "Clash Crytpo HITL tests"
        [
           testGroup "Clash.Crypto.Cipher.AES"
            [ -- we don't test the >128 variants here, as synthesis
              -- times of the downstream tools for these are too
              -- exorbitant.
              testAES @SpecAES.AES128 sem dev settings
            ] ,
          testGroup "Clash.Crypto.Hash.SHA"
            [ -- we don't test the >256 variants here, as synthesis
              -- times of the downstream tools for these are too
              -- exorbitant.
              testSHA @SHA1   sem dev settings
            , testSHA @SHA224 sem dev settings
            , testSHA @SHA256 sem dev settings
            ] ,
          testGroup "Clash.Crypto.Hash.HMAC"
            [ testHMACSHA @SHA256 sem dev settings
            ] ,
          testGroup "Clash.Crypto.ECDSA.Karatsuba"
            [
              testKaratsuba "Karatsuba" sem dev settings
            ] ,
          testGroup "Clash.Crypto.ECDSA.Modulo"
            [
              testModulo "Modulo" sem dev settings
            ] ,
          testGroup "Clash.Crypto.ECDSA.InverseModulo"
            [
              testInverseModulo "BEA" sem dev settings
            , testInverseModulo "FastGCD" sem dev settings
            , testInverseModulo "FltCtmi" sem dev settings
            -- We don't enable the SictMi test because yosys can't synthesize it.
            -- It might be related to the following issue:
            -- https://github.com/YosysHQ/nextpnr/issues/208
            -- , testInverseModulo "SictMi" sem dev settings
            ]
        ]

  testInverseModulo ∷
    String →
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testInverseModulo name sem dev settings
    = test sem dev settings name $ do
        x ← forAll $ generator $ natToNum @Q
        runHitltInverseModulo sem dev settings x
    where
      generator m = Gen.integral (Range.constantFrom (1) 1 (m-1))

  testModulo ∷
    String →
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testModulo name sem dev settings
    = test sem dev settings name $ do
        x ← forAll $ genUnsigned $ Range.linear minBound maxBound
        runHitltModulo sem dev settings x

  testKaratsuba ∷
    String →
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testKaratsuba name sem dev settings
    = test sem dev settings name $ do
        x ← forAll $ genUnsigned $ Range.linear minBound maxBound
        y ← forAll $ genUnsigned $ Range.linear minBound maxBound
        runHitltKaratsuba sem dev settings x y
  testAES ∷
    ∀ alg.
    (KnownAES alg, KnownAESStream alg, AESKeyExpansion alg, CryptoAES alg, Typeable alg) ⇒
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testAES sem dev settings
    | AESFacts alg ← knownAES @alg
    , name ← dropWhile (== '\'') $ show $ typeRep alg
    = test sem dev settings name $ do
        input ← forAll $ Gen.bytes $ Range.linear 80 100
        key ← forAll $ Gen.bytes $ Range.linear 80 100
        runHitltAES @alg sem dev settings input key
  testSHA ∷
    ∀ alg.
    (KnownSHA alg, CryptoHash alg, Typeable alg) ⇒
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testSHA sem dev settings
    | SHAFacts alg ← knownSHA @alg
    , name ← dropWhile (== '\'') $ show $ typeRep alg
    = test sem dev settings name $ do
        bs ← forAll $ Gen.bytes $ Range.linear 80 100
        runHitltSHA @alg sem dev settings bs

  testHMACSHA ∷
    ∀ alg.
    (KnownSHA alg, CryptoHash alg, Typeable alg) ⇒
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testHMACSHA sem dev settings
    | SHAFacts alg ← knownSHA @alg
    , name ← dropWhile (== '\'') $ show $ typeRep alg
    = test sem dev settings ("HMAC" <> name) $ do
        let n = natToNum @(BlockSize alg `Div` 8)
        key ← forAll $ Gen.bytes $ Range.linear 1 n
        msg ← forAll $ Gen.bytes $ Range.linear 1 499
        runHitltHMACSHA @alg sem dev settings key msg

  test ∷
    QSem →
    FilePath →
    SerialPortSettings →
    String →
    PropertyT IO () →
    TestTree
  test sem dev settings name p
    = localOption (HedgehogTestLimit (Just 1))
    $ sequentialTestGroup name AllSucceed
        [ localOption (HedgehogTestLimit (Just 1))
            $ testProperty "build bitstream" $ property
            $ liftIO $ shake [name <> ":bitstream"]
        , withResource
            (upload shake sem dev settings name)
            (const $ return ())
            $ const
            $ localOption (HedgehogTestLimit (Just 100))
            $ testProperty "run HITLT" $ property p
        ]

  shake = withArgs [] . shakeBuild shakeOptions { shakeVerbosity = Silent }
runHitltAES ∷
  ∀ (alg ∷ AES).
  (KnownAES alg, KnownAESStream alg, AESKeyExpansion alg, CryptoAES alg) ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  ByteString →
  ByteString →
  PropertyT IO ()
runHitltAES sem dev settings input key | AESFacts alg ← knownAES @alg =
 let
  bs = escapeAndTerminate (append input key)
  eq = encryptoECB alg input key
 in runHitlt @((Nb alg * Nb alg * Nb alg * Nk alg) `Div` 8) sem dev settings bs eq

runHitltInverseModulo ∷
  QSem →
  FilePath →
  SerialPortSettings →
  Unsigned 256 →
  PropertyT IO ()
runHitltInverseModulo sem dev settings x =
  runHitlt @(256 `Div` 8) sem dev settings bs eq
 where
  bs = pack $ toList $ bitCoerce @_ @(Vec 32 Word8) x
  eq = pack $ toList $ bitCoerce @_ @(Vec (256 `Div` 8) Word8) invMod
  invMod ∷ Unsigned 256
  invMod = fromInteger $ Modular.unMod $ fromMaybe moduloError $ Modular.inv $
           Modular.toMod @Q $ toInteger x
  moduloError =
    error "Since the modulo of the field is prime, the inverse always exists."

runHitltModulo ∷
  QSem →
  FilePath →
  SerialPortSettings →
  Unsigned 256 →
  PropertyT IO ()
runHitltModulo sem dev settings x =
  runHitlt @(256 `Div` 8) sem dev settings bs eq
 where
  bs = pack $ toList $ bitCoerce @_ @(Vec 32 Word8) x
  eq = pack $ toList $ bitCoerce @_ @(Vec (256 `Div` 8) Word8) $ x `mod` natToNum @Q

type HitlKaratsubaIntegerSize = 128
type HitlKaratsubaWordNumber = HitlKaratsubaIntegerSize `Div` 4

runHitltKaratsuba ∷
  QSem →
  FilePath →
  SerialPortSettings →
  Unsigned HitlKaratsubaIntegerSize →
  Unsigned HitlKaratsubaIntegerSize →
  PropertyT IO ()
runHitltKaratsuba sem dev settings x y =
  runHitlt @(HitlKaratsubaWordNumber) sem dev settings bs eq
 where
  bs = pack $ toList $ bitCoerce @_ @(Vec HitlKaratsubaWordNumber Word8) (x,y)
  eq = pack $ toList $ bitCoerce @_ @(Vec _ Word8) $
   resize @_ @_ @(2 * HitlKaratsubaIntegerSize) x * resize y

runHitltSHA ∷
  ∀ (alg ∷ SHA).
  (KnownSHA alg, CryptoHash alg) ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  ByteString →
  PropertyT IO ()
runHitltSHA sem dev settings input | SHAFacts alg ← knownSHA @alg =
 let
  bs = escapeAndTerminate input
  eq = cryptoHash alg input
 in runHitlt @(MessageDigestSize alg `Div` 8) sem dev settings bs eq

runHitltHMACSHA ∷
  ∀ (alg ∷ SHA).
  (KnownSHA alg, CryptoHash alg) ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  ByteString →
  ByteString →
  PropertyT IO ()
runHitltHMACSHA sem dev settings key msg
  | SHAFacts alg ← knownSHA @alg
  = let
      n = natToNum @(BlockSize alg `Div` 8)
      bs = withKeySize (BS.length key)
        <> escape key
        <> escape (BS.replicate (n - BS.length key) 0xFF)
        <> escapeAndTerminate msg
      eq = HMAC.hmac (cryptoHash alg) n key msg
    in
      runHitlt @(MessageDigestSize alg `Div` 8) sem dev settings bs eq
 where
  withKeySize n
    | n > 0x00 && n < 0xFF = BS.pack [ 0x00, toEnum n ]
    | otherwise            = error $ "Invalid key size: " <> show n

upload ∷
  ([String] → IO ()) →
  QSem →
  FilePath →
  SerialPortSettings →
  String →
  IO()
upload shake sem dev settings name
  = bracket_ (waitQSem sem) (signalQSem sem)
  $ hWithSerial dev settings $ \serial → do
      hSetBuffering serial NoBuffering
      -- upload the bitstream
      shake [name <> ":upload"]
      -- wait for the device ready indicator byte once
      TO.timeout hitltTimeoutTime (waitForReadyByte serial)
        >>= maybe (throw $ hitltTimeoutErr 1 BS.empty) return
 where
  waitForReadyByte serial = do
    xs ← hGet serial 1
    unless (maybe False ((== bitCoerce isReadyIndicator) . fst) $ BS.uncons xs)
      $ waitForReadyByte serial

runHitlt ∷
  ∀ (messageSize ∷ Nat). KnownNat messageSize ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  ByteString →
  ByteString →
  PropertyT IO ()
runHitlt sem dev settings bs eq = do
  let pr = concatMap (printf "%02x " ∷ Word8 → String) . unpack

  dutResponse ← liftIO
    $ bracket_ (waitQSem sem) (signalQSem sem)
    $ hWithSerial dev settings $ \serial → do
        hSetBuffering serial NoBuffering
        -- ensure that the receive buffer is empty before we place
        -- the request
        emptyBuffer @messageSize serial
        -- send the request
        hPut serial bs
        -- wait for the response
        let msgSize =  natToNum @messageSize
        TO.timeout hitltTimeoutTime (hGet serial msgSize) >>= \case
          Just x  → return x
          Nothing → hGetNonBlocking serial msgSize
                       >>= throw . hitltTimeoutErr msgSize

  pr dutResponse === pr eq

emptyBuffer ∷
  ∀ (messageSize ∷ Nat). KnownNat messageSize ⇒
  Handle →
  IO ()
emptyBuffer serial = do
  xs ← hGetNonBlocking serial $ natToNum @messageSize
  unless (BS.null xs) $ emptyBuffer @messageSize serial

-- | Serial timeout in microseconds
hitltTimeoutTime ∷ Int
hitltTimeoutTime = 1_000_000

-- | Serial timeout error
hitltTimeoutErr ∷ Int → ByteString → HitltTimeout
hitltTimeoutErr size bs
  | BS.length bs == 0 = HitltTimeout
      $ "Serial Timeout: no resonse received witin "
     <> show hitltTimeoutTime <> " microseconds"
  | otherwise = HitltTimeout
      $ "Serial Timeout: expected to receive " <> show size <> " bytes within "
     <> show hitltTimeoutTime <> " microseconds, but only received: "
     <> show bs

-- Useful for variable-length data.
escapeAndTerminate ∷ ByteString → ByteString
escapeAndTerminate bs = case BS.unsnoc bs of
  Nothing → BS.empty
  Just (bs0, c) → escape bs0
         `append` pack [0x00, 0xFF]
         `append` escape (singleton c)

escape ∷ ByteString → ByteString
escape = BS.concatMap $ \case
  0x00 → pack [0x00, 0x00]
  byte → singleton byte

class CryptoHash (alg ∷ SHA) where
  cryptoHash ∷ Proxy alg → ByteString → ByteString

instance CryptoHash SHA1      where cryptoHash _ = SHA1.hash
instance CryptoHash SHA224    where cryptoHash _ = SHA224.hash
instance CryptoHash SHA256    where cryptoHash _ = SHA256.hash
instance CryptoHash SHA384    where cryptoHash _ = SHA384.hash
instance CryptoHash SHA512    where cryptoHash _ = SHA512.hash
instance CryptoHash SHA512224 where cryptoHash _ = SHA512t.hash 244
instance CryptoHash SHA512256 where cryptoHash _ = SHA512t.hash 256

class CryptoAES (alg ∷ SpecAES.AES) where
  encryptoECB :: Proxy alg -> ByteString -> ByteString -> ByteString
  decryptoECB :: Proxy alg -> ByteString -> ByteString -> ByteString
instance CryptoAES SpecAES.AES128      where 
  encryptoECB ∷ Proxy alg → ByteString -> ByteString -> ByteString
  encryptoECB _ key plainText = case cipherInit key of
    CryptoPassed (cipher1 :: AES128) -> ecbEncrypt cipher1 plainText
    CryptoFailed cipher1 -> error ("Cipher initialization failed" <> show cipher1)
  decryptoECB ∷ Proxy alg → ByteString -> ByteString -> ByteString
  decryptoECB _ key cipherText = case cipherInit key of
    CryptoPassed (cipher1 ∷ AES128)-> ecbDecrypt cipher1 cipherText
    CryptoFailed cipher1 -> error ("Cipher initialization failed" <> show cipher1)


instance CryptoAES SpecAES.AES192    where
  encryptoECB ∷ Proxy alg → ByteString -> ByteString -> ByteString
  encryptoECB _ key plainText = case cipherInit key of
    CryptoPassed (cipher1 :: AES192) -> ecbEncrypt cipher1 plainText
    CryptoFailed cipher1 -> error ("Cipher initialization failed" <> show (cipher1, BS.length key))
  decryptoECB ∷ Proxy alg → ByteString -> ByteString -> ByteString
  decryptoECB _ key cipherText = case cipherInit key of
    CryptoFailed _ -> error "Cipher initialization failed"
    CryptoPassed (cipher1 ∷ AES192)-> ecbDecrypt cipher1 cipherText

instance CryptoAES SpecAES.AES256    where 
  encryptoECB ∷ Proxy alg → ByteString -> ByteString -> ByteString
  encryptoECB _ key plainText = case cipherInit key of
    CryptoPassed (cipher1 :: AES256) -> ecbEncrypt cipher1 plainText
    CryptoFailed cipher1 -> error ("Cipher initialization failed" <> show (cipher1, BS.length key))

  decryptoECB ∷ Proxy alg → ByteString -> ByteString -> ByteString
  decryptoECB _ key cipherText = case cipherInit key of
    CryptoFailed _ -> error "Cipher initialization failed"
    CryptoPassed (cipher1 ∷ AES256)-> ecbDecrypt cipher1 cipherText

parseCS ∷ String → CommSpeed
parseCS = \case
  "110"    → CS110
  "300"    → CS300
  "600"    → CS600
  "1200"   → CS1200
  "2400"   → CS2400
  "4800"   → CS4800
  "9600"   → CS9600
  "19200"  → CS19200
  "38400"  → CS38400
  "57600"  → CS57600
  "115200" → CS115200
  str      → case readMaybe str of
    Nothing → error $ "Invalid baud: " <> str
    Just cs → CS cs

newtype HitltTimeout = HitltTimeout String
instance Show HitltTimeout where show (HitltTimeout msg) = msg
instance Exception HitltTimeout