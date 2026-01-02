{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeAbstractions #-}

{-# OPTIONS_GHC -Wno-deprecations #-}

import Prelude

import Clash.Prelude
  ( type Div, type (*), type (-), type (+)
  , SNat(..), Nat, KnownNat, Unsigned, Vec
  , BitPack(BitSize), Bit, Index, System
  , toList, resize,  bitCoerce, natToNum, testBit, fromList
  , sampleN, withClockResetEnable, clockGen, resetGen, enableGen
  )

import Clash.Hedgehog.Sized.Index (genIndex)
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import Clash.XException (hasUndefined)

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
import Hedgehog (PropertyT, (===), property, forAll, MonadGen)
import Language.Haskell.Unicode (type (≤))
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

import Clash.Sized.Stack (StackAction(..), stack)
import Clash.Crypto.Hash.SHA
  ( SHA(..), MessageDigestSize, KnownSHA, SHAFacts(..), BlockSize, knownSHA
  )
import Clash.Crypto.Calculator.ISA
  ( CluInstruction(..), ECPrime(..), CPrime, CMod, ECMod, SecP256ModPrime
  )
import Clash.Crypto.Calculator.Modulo (Mod, ModSize, createMod)

import Test.Clash.Crypto.Calculator
import Test.Clash.Crypto.Calculator.InverseModulo

import Hitl.Clash.Crypto.Calculator.CLU (CluInput)
import Hitl.Clash.Sized.Stack (StackSize, StackValueSize, StackPadding)
import Hitl.Clash.Cores.Uart.Extra (ByteSize, isReadyIndicator)

import Shake
  ( ShakeOptions(..), Verbosity(..)
  , shakeOptions, shakeBuild, configLookup
  )

import qualified Data.ByteArray      as Memory (unpack)
import qualified Data.ByteString     as BS
  ( concatMap, empty, null, uncons, unsnoc, pack, length, replicate
  )
import qualified Data.List           as List
import qualified System.Timeout      as TO (timeout)
import qualified Hedgehog.Range      as Range (linear)
import qualified Hedgehog.Gen        as Gen
import qualified Clash.Sized.Vector  as Vec
import qualified Crypto.Hash         as Hash
import qualified Crypto.MAC.HMAC     as HMAC

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
    = defaultMain
    $ localOption (HedgehogTestLimit (Just 100))
    $ testGroup "Clash Crytpo HITL tests"
        [ localOption (HedgehogTestLimit (Just 10))
        $ testGroup "Clash.Sized.Stack"
            [ testStack "Stack" sem dev settings
            ]
        , testGroup "Clash.Crypto.Hash.SHA"
            [ -- we don't test the >256 variants here, as synthesis
              -- times of the downstream tools for these are too
              -- exorbitant.
              testSHA SHA1   sem dev settings
            , testSHA SHA224 sem dev settings
            , testSHA SHA256 sem dev settings
            ]
        , testGroup "Clash.Crypto.Hash.HMAC"
            [ testHMACSHA SHA256 sem dev settings
            ]
        , testGroup "Clash.Crypto.Calculator.Karatsuba"
            [ testKaratsuba "Karatsuba" sem dev settings
            , testKaratsubaModulo "KaratsubaModulo" sem dev settings
            ]
        , testGroup "Clash.Crypto.Calculator.Modulo"
            [ testModulo "Modulo" sem dev settings
            ]
        , testGroup "Clash.Crypto.Calculator.InverseModulo"
            [ testInverseModulo "BEA" sem dev settings
            , testInverseModulo "FastGCD" sem dev settings
            , testInverseModulo "FltCtmi" sem dev settings
            -- We don't enable the SictMi test because yosys can't synthesize it.
            -- It might be related to the following issue:
            -- https://github.com/YosysHQ/nextpnr/issues/208
            -- , testInverseModulo "SictMi" sem dev settings
            ]
        , testGroup "Clash.Crypto.Calculator.CLU"
            [ testCLU "CLU" sem dev settings
            ]
        , testGroup "Clash.Crypto.Calculator"
            [ testCalculator "Calculator" sem dev settings
            ]
        ]

  testCLU ∷
    String →
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testCLU name sem dev settings
    = test sem dev settings name $ do
        opMod ← forAll Gen.enumBounded
        a ∷ CMod SecP256Mod ← genMod
        b ∷ CMod SecP256Mod ← genMod
        runHitltCLU sem dev settings (opMod, (a, b))

        opOrd ← forAll Gen.enumBounded
        c ∷ CMod SecP256Ord ← genMod
        d ∷ CMod SecP256Ord ← genMod
        runHitltCLU sem dev settings (opOrd, (c, d))

  testCalculator ∷
    String →
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testCalculator name sem dev settings
    = test sem dev settings name $ do
        a ∷ CMod SecP256Mod ← genMod
        b ∷ CMod SecP256Mod ← genMod
        runHitltCalculator sem dev settings a b

  genStackAction ∷
    ∀ n size m.
    (KnownNat n, KnownNat size, MonadGen m) ⇒
    m (StackAction n (Unsigned size))
  genStackAction = Gen.choice
    [
      Push    <$> genUnsigned (Range.linear minBound maxBound)
    , Pop     <$> genIndex    (Range.linear minBound maxBound)
    , Inspect <$> genIndex    (Range.linear minBound maxBound)
    , CopyUp  <$> genIndex    (Range.linear minBound maxBound)
    , Swap    <$> genIndex    (Range.linear minBound maxBound)
    ]

  testStack ∷
    String →
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testStack name sem dev settings
    | SNat @s ← SNat @( BitSize
                          ( Unsigned StackPadding
                          , ( Maybe (Unsigned StackValueSize)
                            , Index (StackSize + 1)
                            )
                          ) `Div` 8
                      )
    = test sem dev settings name $ do
        actions <- forAll $ Gen.list (Range.linear 20 1000) $
                   genStackAction @StackSize @StackValueSize
        runStack s sem dev settings actions

  testInverseModulo ∷
    String →
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testInverseModulo name sem dev settings
    = test sem dev settings name $ do
        x ∷ ECMod ← genMod
        unless (x == 0)
          $ runHitltInverseModulo sem dev settings x

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

  testKaratsubaModulo ∷
    String →
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testKaratsubaModulo name sem dev settings
    = test sem dev settings name $ do
        x ∷ ECMod ← genMod
        y ∷ ECMod ← genMod
        runHitltKaratsubaModulo sem dev settings x y

  testSHA ∷
    ∀ alg → (KnownSHA alg, CryptoHash alg, Typeable alg,
             Hash.HashAlgorithm (CryptoToHash alg)) ⇒
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testSHA alg sem dev settings
    | SHAFacts ← knownSHA alg
    , name ← dropWhile (== '\'') $ show $ typeRep (Proxy @alg)
    = test sem dev settings name $ do
        bs ← forAll $ Gen.bytes $ Range.linear 80 100
        runHitltSHA alg sem dev settings bs

  testHMACSHA ∷
    ∀ alg → (KnownSHA alg, CryptoHash alg, Typeable alg,
             Hash.HashAlgorithm (CryptoToHash alg)) ⇒
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testHMACSHA alg sem dev settings
    | SHAFacts ← knownSHA alg
    , name ← dropWhile (== '\'') $ show $ typeRep (Proxy @alg)
    = test sem dev settings ("HMAC" <> name) $ do
        let n = natToNum @(BlockSize alg `Div` 8)
        key ← forAll $ Gen.bytes $ Range.linear 1 n
        msg ← forAll $ Gen.bytes $ Range.linear 1 499
        runHitltHMACSHA alg sem dev settings key msg

  test ∷
    QSem →
    FilePath →
    SerialPortSettings →
    String →
    PropertyT IO () →
    TestTree
  test sem dev settings name p
    = sequentialTestGroup name AllSucceed
        [ localOption (HedgehogTestLimit (Just 1))
            $ testProperty "build bitstream" $ property
            $ liftIO $ shake [name <> ":bitstream"]
        , withResource
            (upload shake sem dev settings name)
            (const $ return ())
            $ const
            $ testProperty "run HITLT" $ property p
        ]

  shake = withArgs [] . shakeBuild shakeOptions { shakeVerbosity = Silent }

runHitltCLU ∷
  ∀ (p ∷ Nat). (KnownNat p, 1 ≤ p, ModSize p ~ ModSize (CPrime SecP256Mod)) ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  (CluInstruction, (Mod p, Mod p)) →
  PropertyT IO ()
runHitltCLU sem dev settings (op, (x, y)) =
  runHitlt (ModSize p `Div` 8) sem dev settings bs eq
 where
  bs = pack $ toList
     $ bitCoerce @_ @(ByteVec (ByteSize CluInput))
         ((0, (op, ((bitCoerce x, bitCoerce y), pV))) ∷ CluInput)

  eq = pack $ toList
    $ bitCoerce @_ @(ByteVec (ByteSize ECMod))
    $ case op of
        Add → x + y
        Sub → x - y
        Mul → x * y
        Inv | x == 0 → y
            | otherwise → invMod x
        Bit | y < natToNum @(ModSize p), testBit x (fromEnum y) → 1
            | otherwise → 0

  pV = natToNum @(p - 1) + 1

runHitltCalculator ∷
  QSem →
  FilePath →
  SerialPortSettings →
  ECMod → ECMod →
  PropertyT IO ()
runHitltCalculator sem dev settings a b =
  runHitlt (ByteSize ECMod) sem dev settings bs eq
 where
  bs = pack $ toList
     $ bitCoerce @_ @(ByteVec (ByteSize (ECMod, ECMod))) (a, b)
  eq = pack $ toList $ bitCoerce @_ @(ByteVec (ByteSize ECMod))
     $ goldenRoutine a b

runStack ∷
  ∀ messageSize → KnownNat messageSize ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  [StackAction StackSize (Unsigned StackValueSize)] →
  PropertyT IO ()
runStack messageSize sem dev settings actions = do
  let bsAction = pack . toList . bitCoerce
       . fmap (\b -> if hasUndefined b then 0 else b) . bitCoerce @_ @(Vec _ Bit)
  -- If we run the test multiple times, we want to empty the stack.
  let actionList = Pop (natToNum @(StackSize)) : actions
  dutResponses ← liftIO $ bracket_ (waitQSem sem) (signalQSem sem)
   $ mapM (sendRequest messageSize dev settings . bsAction) actionList

  let simResponses
            = sampleN @System (List.length actions + 3)
            $ withClockResetEnable clockGen resetGen enableGen
            $ stack @_ @StackSize @(Unsigned StackValueSize)
            $ fromList
            $ Pop 0 : actionList <> [Pop 0]
  let boardResponses = map (snd . bitCoerce @_ @(Unsigned StackPadding, _)
       . fromMaybe (error "unthinkable") . Vec.fromList . unpack) dutResponses

  let safeTail = maybe (error "unthinkable") snd . List.uncons
  boardResponses === safeTail (safeTail simResponses)

runHitltInverseModulo ∷
  QSem →
  FilePath →
  SerialPortSettings →
  ECMod →
  PropertyT IO ()
runHitltInverseModulo sem dev settings x = do
  runHitlt (ByteSize ECMod) sem dev settings (toBS x)
    $ toBS $ invMod @SecP256ModPrime x
 where
  toBS = pack . toList . bitCoerce @_ @(ByteVec (ByteSize ECMod))

runHitltModulo ∷
  QSem →
  FilePath →
  SerialPortSettings →
  Unsigned 256 →
  PropertyT IO ()
runHitltModulo sem dev settings x =
  runHitlt (ByteSize (Unsigned 256)) sem dev settings bs eq
 where
  bs = pack $ toList $ bitCoerce @_ @(ByteVec (ByteSize (Unsigned 256))) x
  eq = pack $ toList $ bitCoerce @_ @(ByteVec (ByteSize (Unsigned 256)))
     $ x `mod` natToNum @SecP256ModPrime

type HitlKaratsubaIntegerSize = 256
type HitlKaratsubaWordNumber = HitlKaratsubaIntegerSize `Div` 4

runHitltKaratsuba ∷
  QSem →
  FilePath →
  SerialPortSettings →
  Unsigned HitlKaratsubaIntegerSize →
  Unsigned HitlKaratsubaIntegerSize →
  PropertyT IO ()
runHitltKaratsuba sem dev settings x y =
  runHitlt HitlKaratsubaWordNumber sem dev settings bs eq
 where
  bs = pack $ toList $ bitCoerce @_ @(ByteVec HitlKaratsubaWordNumber) (x,y)
  eq = pack $ toList $ bitCoerce @_ @(ByteVec _) $
   resize @_ @_ @(2 * HitlKaratsubaIntegerSize) x * resize y

runHitltKaratsubaModulo ∷
  QSem →
  FilePath →
  SerialPortSettings →
  ECMod →
  ECMod →
  PropertyT IO ()
runHitltKaratsubaModulo sem dev settings x y =
  runHitlt (ByteSize ECMod) sem dev settings bs eq
 where
  bs = pack $ toList $ bitCoerce @_ @(ByteVec (2 * (ByteSize ECMod))) (x, y)
  eq = pack $ toList $ bitCoerce @_ @(ByteVec (ByteSize ECMod)) $ x * y

runHitltSHA ∷
  ∀ (alg ∷ SHA) →
  (KnownSHA alg, CryptoHash alg, Hash.HashAlgorithm (CryptoToHash alg)) ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  ByteString →
  PropertyT IO ()
runHitltSHA alg sem dev settings input | SHAFacts ← knownSHA alg =
 let
  bs = escapeAndTerminate input
  eq = cryptoHash alg input
 in runHitlt (MessageDigestSize alg `Div` 8) sem dev settings bs eq

runHitltHMACSHA ∷
  ∀ (alg ∷ SHA) →
  (KnownSHA alg, CryptoHash alg, Hash.HashAlgorithm (CryptoToHash alg)) ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  ByteString →
  ByteString →
  PropertyT IO ()
runHitltHMACSHA alg sem dev settings key msg
  | SHAFacts ← knownSHA alg
  = let
      n = natToNum @(BlockSize alg `Div` 8)
      bs = withKeySize (BS.length key)
        <> escape key
        <> escape (BS.replicate (n - BS.length key) 0xFF)
        <> escapeAndTerminate msg
      eq = BS.pack $ Memory.unpack
         $ HMAC.hmacGetDigest $ HMAC.hmac @_ @_ @(CryptoToHash alg) key msg
    in
      runHitlt (MessageDigestSize alg `Div` 8) sem dev settings bs eq
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
  ∀ (messageSize ∷ Nat) → KnownNat messageSize ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  ByteString →
  ByteString →
  PropertyT IO ()
runHitlt messageSize sem dev settings bs eq = do
  let pr = concatMap (printf "%02x " ∷ Word8 → String) . unpack

  dutResponse ← liftIO
    $ bracket_ (waitQSem sem) (signalQSem sem)
    $ sendRequest messageSize dev settings bs

  pr dutResponse === pr eq

sendRequest ∷
  ∀ (messageSize ∷ Nat) → KnownNat messageSize ⇒
  FilePath →
  SerialPortSettings →
  ByteString →
  IO ByteString
sendRequest messageSize dev settings bs =
  hWithSerial dev settings $ \serial → do
    hSetBuffering serial NoBuffering
    -- ensure that the receive buffer is empty before we place
    -- the request
    emptyBuffer messageSize serial
    -- send the request
    hPut serial bs
    -- wait for a response
    let msgSize = natToNum @messageSize
    TO.timeout hitltTimeoutTime (hGet serial msgSize) >>= \case
      Just x  → return x
      Nothing → hGetNonBlocking serial msgSize
                   >>= throw . hitltTimeoutErr msgSize

emptyBuffer ∷
  ∀ (messageSize ∷ Nat) → KnownNat messageSize ⇒
  Handle →
  IO ()
emptyBuffer messageSize serial = do
  xs ← hGetNonBlocking serial $ natToNum @messageSize
  unless (BS.null xs) $ emptyBuffer messageSize serial

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

genMod ∷ ∀ p m. (Monad m, KnownNat p, 3 ≤ p) ⇒ PropertyT m (Mod p)
genMod = do
  x ← forAll $ genIndex @p $ Range.linear minBound maxBound
  return $ createMod @p x

class CryptoHash (alg ∷ SHA) where
  type CryptoToHash (alg ∷ SHA)
  cryptoHash# ∷ Proxy alg → ByteString → Hash.Digest (CryptoToHash alg)

instance CryptoHash SHA1 where
  type CryptoToHash SHA1 = Hash.SHA1
  cryptoHash# _ = Hash.hash
instance CryptoHash SHA224 where
  type CryptoToHash SHA224  = Hash.SHA224
  cryptoHash# _ = Hash.hash
instance CryptoHash SHA256 where
  type CryptoToHash SHA256  = Hash.SHA256
  cryptoHash# _ = Hash.hash
instance CryptoHash SHA384 where
  type CryptoToHash SHA384  = Hash.SHA384
  cryptoHash# _ = Hash.hash
instance CryptoHash SHA512 where
  type CryptoToHash SHA512 = Hash.SHA512
  cryptoHash# _ = Hash.hash
instance CryptoHash SHA512224 where
  type CryptoToHash SHA512224  = Hash.SHA512t_224
  cryptoHash# _ = Hash.hash
instance CryptoHash SHA512256 where
  type CryptoToHash SHA512256  = Hash.SHA512t_256
  cryptoHash# _ = Hash.hash

cryptoHash ∷
 ∀ (alg ∷ SHA) → CryptoHash alg ⇒ ByteString → ByteString
cryptoHash alg = BS.pack . Memory.unpack . cryptoHash# (Proxy @alg)

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

type ByteVec n = Vec n Word8
