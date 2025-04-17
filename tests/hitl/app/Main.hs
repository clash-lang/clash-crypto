{-# LANGUAGE AllowAmbiguousTypes #-}

import Prelude

import Control.Concurrent.QSem (QSem, newQSem, waitQSem, signalQSem)
import Control.Exception
  ( SomeException, Exception, Handler(..)
  , catches, throw, bracket_
  )
import Control.Monad.IO.Class (liftIO)
import Data.ByteString
  ( ByteString
  , append, hGet, hGetNonBlocking, hPut, pack, unpack, singleton
  )
import Data.Proxy (Proxy(..))
import Data.Typeable (Typeable, typeRep)
import Data.Word (Word8)
import Hedgehog (PropertyT, (===), property, forAll)
import System.Exit (ExitCode, exitWith)
import System.Environment (setEnv, withArgs)
import System.Hardware.Serialport
  ( SerialPortSettings(..), CommSpeed(..)
  , defaultSerialSettings, hWithSerial
  )
import System.IO (BufferMode(..), hSetBuffering)
import Test.Tasty
 (TestTree, DependencyType(..), defaultMain, localOption, sequentialTestGroup)
import Test.Tasty.Hedgehog (HedgehogTestLimit(..), testProperty)
import Text.Printf (printf)
import Text.Read (readMaybe)

import qualified Data.ByteString as BS (concatMap, null)
import qualified System.Timeout  as TO (timeout)

import qualified Hedgehog.Gen   as Gen (bytes)
import qualified Hedgehog.Range as Range (linear)

import Clash.Hedgehog.Sized.Unsigned (genUnsigned)

import qualified Crypto.Hash.SHA1    as SHA1 (hash)
import qualified Crypto.Hash.SHA224  as SHA224 (hash)
import qualified Crypto.Hash.SHA256  as SHA256 (hash)
import qualified Crypto.Hash.SHA384  as SHA384 (hash)
import qualified Crypto.Hash.SHA512  as SHA512 (hash)
import qualified Crypto.Hash.SHA512t as SHA512t (hash)

import Clash.Prelude (type Div, natToNum, Unsigned, bitCoerce, Vec, toList, resize, Nat, KnownNat)
import Clash.Crypto.Hash.SHA
  ( SHA(..), MessageDigestSize, KnownSHA(..), SHAFacts(..)
  )
import Shake
  ( ShakeOptions(..), Verbosity(..)
  , shakeOptions, shakeBuild, configLookup
  )

main ∷ IO ()
main = do
  lkup <- configLookup

  let serialDev = lkup "HITLT_SERIAL_DEV"
      serialSpeed = lkup "SERIAL_SPEED"
      settings = defaultSerialSettings { commSpeed = parseCS serialSpeed }

  -- using only a single serial forces us to use single threaded test
  -- executation at this points
  setEnv "TASTY_NUM_THREADS" "1"

  sem <- newQSem 1

  run sem serialDev settings `catches`
    [ Handler $ \(e :: ExitCode) -> exitWith e
    , Handler $ \(e :: SomeException) -> error $ show e
    ]
 where
  run sem dev settings
    = defaultMain $ sequentialTestGroup "Clash Crytpo HITL tests" AllSucceed
        [
          sequentialTestGroup "Clash.Crypto.Hash.SHA" AllSucceed
            [ -- we don't test the >256 variants here, as synthesis
              -- times of the downstream tools for these are too
              -- exorbitant.
              testSHA @SHA1   sem dev settings
            , testSHA @SHA224 sem dev settings
            , testSHA @SHA256 sem dev settings
            ] ,
          sequentialTestGroup "Clash.Crypto.ECDSA.Karatsuba" AllSucceed
            [
              testKaratsuba "Karatsuba" sem dev settings
            ]
        ]

  testKaratsuba ::
    String ->
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testKaratsuba name sem dev settings
    = test name $ do
        x <- forAll $ genUnsigned $ Range.linear minBound maxBound
        y <- forAll $ genUnsigned $ Range.linear minBound maxBound
        runHitltKaratsuba sem dev settings x y

  testSHA ::
    forall alg.
    (KnownSHA alg, CryptoHash alg, Typeable alg) =>
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testSHA sem dev settings
    | SHAFacts alg <- knownSHA @alg
    , name <- dropWhile (== '\'') $ show $ typeRep alg
    = test name $ do
        bs ← forAll $ Gen.bytes $ Range.linear 80 100
        runHitltSHA @alg sem dev settings bs

  test ::
    String ->
    PropertyT IO () ->
    TestTree
  test name p
    = localOption (HedgehogTestLimit (Just 1))
    $ sequentialTestGroup name AllSucceed
        [ localOption (HedgehogTestLimit (Just 1))
            $ testProperty "build bitstream" $ property
            $ liftIO $ shake [name <> ":bitstream"]
        , localOption (HedgehogTestLimit (Just 1))
            $ testProperty "write bitstream" $ property
            $ liftIO $ shake [name <> ":upload"]
        , localOption (HedgehogTestLimit (Just 100))
            $ testProperty "run HITLT" $ property p
        ]

  shake = withArgs [] . shakeBuild shakeOptions { shakeVerbosity = Silent }

runHitltKaratsuba ∷
  QSem →
  FilePath →
  SerialPortSettings →
  Unsigned 128 →
  Unsigned 128 -> 
  PropertyT IO ()
runHitltKaratsuba sem dev settings x y =
  runHitlt @(256 `Div` 8) sem dev settings bs eq
 where
  bs = pack $ toList $ bitCoerce @_ @(Vec 32 Word8) (x,y)
  eq = pack $ toList $ bitCoerce @_ @(Vec (256 `Div` 8) Word8) $ resize x * resize y

runHitltSHA ∷
  ∀ (alg :: SHA).
  (KnownSHA alg, CryptoHash alg) ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  ByteString →
  PropertyT IO ()
runHitltSHA sem dev settings input | SHAFacts alg <- knownSHA @alg =
 let
  bs = escapeAndTerminate input
  eq = cryptoHash alg input
 in runHitlt @(MessageDigestSize alg `Div` 8) sem dev settings bs eq

runHitlt ∷ forall (messageSize :: Nat). KnownNat messageSize =>
  QSem →
  FilePath →
  SerialPortSettings →
  ByteString ->
  ByteString ->
  PropertyT IO ()
runHitlt sem dev settings bs eq = do
  let resultSize =
        natToNum @messageSize

      pr = concatMap (printf "%02x " :: Word8 -> String) . unpack

      emptyBuffer serial = do
        xs <- hGetNonBlocking serial resultSize
        if BS.null xs
          then return ()
          else emptyBuffer serial

      -- timeout in microseconds
      hitltTimeoutTime = 1_000_000 :: Int

      hitltTimeoutErr = HitltTimeout
        $ "Serial Timout: no resonse received witin "
             <> show hitltTimeoutTime <> " seconds"

  dutResponse <- liftIO
    $ bracket_ (waitQSem sem) (signalQSem sem)
    $ hWithSerial dev settings $ \serial → do
        hSetBuffering serial NoBuffering
        -- ensure that the receive buffer is empty before we place
        -- the request
        emptyBuffer serial
        -- send the request
        hPut serial bs
        -- wait for the response
        TO.timeout hitltTimeoutTime (hGet serial resultSize)
          >>= maybe (throw hitltTimeoutErr) return
  pr dutResponse === pr eq

escapeAndTerminate :: ByteString -> ByteString
escapeAndTerminate = terminate . escape
 where
  terminate = (`append` pack [0x00, 0x80])
  escape = BS.concatMap $ \case
    0x00 -> pack [0x00, 0x00]
    byte -> singleton byte

class CryptoHash (alg :: SHA) where
  cryptoHash :: Proxy alg -> ByteString → ByteString

instance CryptoHash SHA1      where cryptoHash _ = SHA1.hash
instance CryptoHash SHA224    where cryptoHash _ = SHA224.hash
instance CryptoHash SHA256    where cryptoHash _ = SHA256.hash
instance CryptoHash SHA384    where cryptoHash _ = SHA384.hash
instance CryptoHash SHA512    where cryptoHash _ = SHA512.hash
instance CryptoHash SHA512224 where cryptoHash _ = SHA512t.hash 244
instance CryptoHash SHA512256 where cryptoHash _ = SHA512t.hash 256

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
    Nothing -> error $ "Invalid baud: " <> str
    Just cs -> CS cs

newtype HitltTimeout = HitltTimeout String
instance Show HitltTimeout where show (HitltTimeout msg) = msg
instance Exception HitltTimeout
