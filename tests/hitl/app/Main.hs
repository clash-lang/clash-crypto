{-|
Copyright   : Copyright © 2024-2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Hardware-in-the-loop host controller loading the FPGA bitstreams on
the device under test and generating property test based inputs for
the different test cases.
-}

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeAbstractions #-}

{-# OPTIONS_GHC -Wno-deprecations #-}

import Prelude

import Clash.Prelude.Safe
  ( type Div, type (*), type (-), type (+)
  , SNat(..), Nat, KnownNat, Unsigned, Vec
  , BitPack(BitSize), Bit, Index, System
  , toList, resize,  bitCoerce, natToNum, testBit, fromList
  , sampleN, withClockResetEnable, clockGen, resetGen, enableGen
  )

import qualified Clash.Prelude.Safe as BV (unpack)

import Clash.Hedgehog.Sized.Index (genIndex)
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import Clash.XException (hasUndefined)

import Control.Concurrent.QSem (QSem, newQSem, waitQSem, signalQSem)
import Control.Exception
  ( SomeException, Exception, Handler(..)
  , catches, throw, bracket_
  )
import Control.Monad (unless, void)
import Control.Monad.IO.Class (liftIO)
import Data.Bifunctor (bimap)
import Data.ByteString
  ( ByteString
  , append, hGet, hGetNonBlocking, hPut, pack, unpack, singleton
  )
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy(..))
import Data.Tuple (swap)
import Data.Typeable (Typeable, typeRep)
import Data.Word (Word8)
import GHC.IO.Handle (Handle)
import Hedgehog (PropertyT, (===), property, forAll, MonadGen)
import Language.Haskell.Unicode (type (≤))
import System.Exit (ExitCode, exitWith)
import System.Environment (setEnv)
import System.Hardware.Serialport
  ( SerialPortSettings(..), CommSpeed(..)
  , defaultSerialSettings, hWithSerial
  )
import System.IO (BufferMode(..), hSetBuffering)
import System.Process
  ( readCreateProcess, CreateProcess(..), proc, StdStream(..)
  )
import Test.Tasty
  ( TestTree, DependencyType(..)
  , defaultMain, localOption, sequentialTestGroup, testGroup, withResource
  )
import Test.Tasty.Hedgehog (HedgehogTestLimit(..), testProperty)
import Text.Printf (printf)

import Clash.Sized.Stack (StackAction(..), stack)
import Clash.Crypto.Hash.SHA
  ( SHA(..), MessageDigestSize, KnownSHA, SHAFacts(..), BlockSize, knownSHA,
  Digest
  )
import Clash.Crypto.Calculator.ISA
  ( CluInstruction(..), SecP256ModPrime, SecP256OrdPrime, ArgCount, ResultCount
  )
import Clash.Crypto.Calculator.Modulo (ℤₘ, PrimeField, ModSize, createMod)

import Test.Clash.Crypto.Calculator
import Test.Clash.Crypto.Calculator.InverseModulo
import Test.Clash.Crypto.Hash.SHA

import Hitl.Clash.Crypto.Calculator.CLU (CluInput)
import Hitl.Clash.Sized.Stack (StackSize, StackValueSize, StackPadding)
import Hitl.Clash.Cores.Uart.Extra (ByteSize, isReadyIndicator)
import Hitl.Clash.Crypto.PubKey.ECDSA

import Data.Constraint.Nat.Extra (CancelMultiple)
import GHC.TypeNats.Proof (Rewrite(..), using)

import qualified Data.ByteArray      as Memory (unpack)
import qualified Data.ByteString     as BS
  ( concatMap, empty, null, uncons, unsnoc, pack, length, replicate, tail
  )
import qualified Data.List           as List
import qualified System.Timeout      as TO (timeout)
import qualified Hedgehog.Range      as Range (linear)
import qualified Hedgehog.Gen        as Gen
import qualified Clash.Sized.Vector  as Vec
import qualified Crypto.Hash         as Hash
import qualified Crypto.MAC.HMAC     as HMAC
import Crypto.ECC (Curve_P256R1, EllipticCurve (..))
import Crypto.Error (throwCryptoError)
import Crypto.PubKey.ECDSA
  ( signDigestWith, decodePrivate, signatureToIntegers, toPublic, encodePublic
  )
import qualified Crypto.PubKey.ECC.ECDSA as Spec
import qualified Crypto.PubKey.ECC.Types as Spec

type HitlTestTree = String → QSem → FilePath → SerialPortSettings → TestTree

-- | Serial timeout in microseconds
hitltTimeoutTime ∷ Int
hitltTimeoutTime = 10_000_000

main ∷ IO ()
main = do
  serialDev   ← nixConfig "hitlt-serial-dev"
  serialSpeed ← nixConfig "serial-speed"
  let settings = defaultSerialSettings { commSpeed = parseCS serialSpeed }

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
            -- The SictMi test has been disabled due to a bug in nextpnr
            -- cf. https://github.com/clash-lang/clash-crypto/issues/65
            --, testInverseModulo "SictMi" sem dev settings
            ]
        , testGroup "Clash.Crypto.Calculator.CLU"
            [ testCLU "CLU" sem dev settings
            ]
        , testGroup "Clash.Crypto.Calculator"
            [ testCalculator "Calculator" sem dev settings
            ]
        , testGroup "Clash.Crypto.PubKey.ECDSA.Nonce.Deterministic"
            [ testDeterministicNonce SHA256 "DeterministicNonce" sem dev
                                     settings
            ]
        , localOption (HedgehogTestLimit (Just 5))
        $ testGroup "Clash.Crypto.PubKey.ECDSA"
            [ testPubKeyAlgorithm "ECDSASign" sem dev settings
            , testDerivePublicKey "ECDSADerivePublicKey" sem dev settings
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
        a ∷ PrimeField SecP256ModPrime ← genMod
        b ∷ PrimeField SecP256ModPrime ← genMod
        runHitltCLU sem dev settings (opMod, (a, b))

        opOrd ← forAll Gen.enumBounded
        c ∷ PrimeField SecP256OrdPrime ← genMod
        d ∷ PrimeField SecP256OrdPrime ← genMod
        runHitltCLU sem dev settings (opOrd, (c, d))

  testCalculator ∷
    String →
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testCalculator name sem dev settings
    = test sem dev settings name $ do
        a ∷ PrimeField SecP256ModPrime ← genMod
        b ∷ PrimeField SecP256ModPrime ← genMod
        runHitltCalculator sem dev settings a b

  testPubKeyAlgorithm ∷
    String →
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testPubKeyAlgorithm name sem dev settings
    = test sem dev settings name $ do
        h ∷ PrimeField SecP256ModPrime ← genMod
        k ∷ PrimeField SecP256ModPrime ← genModBounded 1 maxBound
        d ∷ PrimeField SecP256ModPrime ← genModBounded 1 maxBound
        runHitltPubKeyAlgorithm sem dev settings
         (bitCoerce h) (bitCoerce k) (bitCoerce d)

  testDerivePublicKey ∷
    String →
    QSem →
    FilePath →
    SerialPortSettings →
    TestTree
  testDerivePublicKey name sem dev settings
    = test sem dev settings name $ do
        d ∷ PrimeField SecP256ModPrime ← genModBounded 1 maxBound
        runHitltDerivePublicKey sem dev settings $ bitCoerce d

  genStackAction ∷
    ∀ n size m.
    (KnownNat n, KnownNat size, MonadGen m) ⇒
    m (StackAction n (Unsigned size))
  genStackAction = Gen.choice
    [ Push    <$> genUnsigned (Range.linear minBound maxBound)
    , Pop     <$> genIndex    (Range.linear minBound maxBound)
    , Inspect <$> genIndex    (Range.linear minBound maxBound)
    , CopyUp  <$> genIndex    (Range.linear minBound maxBound)
    , Swap    <$> genIndex    (Range.linear minBound maxBound)
    ]

  testStack ∷ HitlTestTree
  testStack name sem dev settings
    | SNat @s ← SNat @( BitSize
                          ( Unsigned StackPadding
                          , ( Maybe (Unsigned StackValueSize)
                            , Index (StackSize + 1)
                            )
                          ) `Div` 8
                      )
    = test sem dev settings name $ do
        actions ← forAll $ Gen.list (Range.linear 20 1000) $
                  genStackAction @StackSize @StackValueSize
        runStack s sem dev settings actions

  testInverseModulo ∷ HitlTestTree
  testInverseModulo name sem dev settings
    = test sem dev settings name $ do
        x ∷ PrimeField SecP256ModPrime ← genMod
        unless (x == 0)
          $ runHitltInverseModulo sem dev settings x

  testModulo ∷ HitlTestTree
  testModulo name sem dev settings
    = test sem dev settings name $ do
        x ← forAll $ genUnsigned $ Range.linear minBound maxBound
        runHitltModulo sem dev settings x

  testKaratsuba ∷ HitlTestTree
  testKaratsuba name sem dev settings
    = test sem dev settings name $ do
        x ← forAll $ genUnsigned $ Range.linear minBound maxBound
        y ← forAll $ genUnsigned $ Range.linear minBound maxBound
        runHitltKaratsuba sem dev settings x y

  testKaratsubaModulo ∷ HitlTestTree
  testKaratsubaModulo name sem dev settings
    = test sem dev settings name $ do
        x ∷ PrimeField SecP256ModPrime ← genMod
        y ∷ PrimeField SecP256ModPrime ← genMod
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

  testDeterministicNonce ∷
    ∀ alg → (KnownSHA alg, CryptoHash alg, Typeable alg,
             Hash.HashAlgorithm (CryptoToHash alg)) ⇒
    HitlTestTree
  testDeterministicNonce alg name sem dev settings
    = test sem dev settings name $ do
        let m = natToNum @(SecP256OrdPrime - 1)
        bs ← forAll $ Gen.bytes $ Range.linear 1 1000
        pk ← forAll $ Gen.integral $ Range.linear 1 m
        runHitltDeterministicNonce alg sem dev settings bs pk

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
            $ liftIO $ nixBuild name
        , withResource
            (upload sem dev settings name)
            (const $ return ())
            $ const
            $ testProperty "run HITLT" $ property p
        ]

readProcessSilently ∷ FilePath → [String] → IO String
readProcessSilently path args = readCreateProcess silentProc ""
 where
  baseProc = proc path args
  silentProc = baseProc { std_err = CreatePipe }

callProcessSilently ∷ FilePath → [String] → IO ()
callProcessSilently path args =
  void $ readProcessSilently path args

nixBuild ∷ String → IO ()
nixBuild attr = callProcessSilently "nix" ["run", ".#realize", attr]

nixRun ∷ String → IO ()
nixRun attr = callProcessSilently "nix" ["run", attr]

nixConfig ∷ String → IO String
nixConfig key =
  readProcessSilently "nix" ["eval", "--raw", "--file", "build-config.nix", key]

runHitltCLU ∷
  ∀ (p ∷ Nat). (KnownNat p, 1 ≤ p, ModSize p ~ ModSize SecP256ModPrime) ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  (CluInstruction, (PrimeField p, PrimeField p)) →
  PropertyT IO ()
runHitltCLU sem dev settings (op, (x, y)) =
  runHitlt (ModSize p `Div` 8) sem dev settings bs eq
 where
  bs = pack $ toList
     $ bitCoerce @_ @(ByteVec (ByteSize CluInput))
         ((0, (op, ((bitCoerce x, bitCoerce y), pV))) ∷ CluInput)

  eq = pack $ toList
    $ bitCoerce @_ @(ByteVec (ByteSize (PrimeField SecP256ModPrime)))
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
  (ArgCount Main ~ 2, ResultCount Main ~ 1) ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  PrimeField SecP256ModPrime →
  PrimeField SecP256ModPrime →
  PropertyT IO ()
runHitltCalculator sem dev settings a b =
  runHitlt (type (ResultCount Main * ByteSize (PrimeField SecP256ModPrime)))
           sem dev settings bs eq
 where
  bs = pack $ toList
     $ bitCoerce @_ @(ByteVec (ArgCount Main * ByteSize (PrimeField SecP256ModPrime)))
       (a, b)
  eq = pack
     $ toList
     $ bitCoerce @_ @(ByteVec (ResultCount Main * ByteSize (PrimeField SecP256ModPrime)))
     $ goldenRoutine a b

runHitltPubKeyAlgorithm ∷
  (ArgCount SignHashTest ~ 3, ResultCount SignHashTest ~ 2) ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  Unsigned 256 → Unsigned 256 → Unsigned 256 →
  PropertyT IO ()
runHitltPubKeyAlgorithm sem dev settings h k d =
  runHitlt (type (ByteSize (Unsigned 256) * ResultCount SignHashTest))
           sem dev settings bs eq
 where
  bs = pack $ toList
     $ bitCoerce @_ @(ByteVec (ArgCount SignHashTest * ByteSize (Unsigned 256)))
       (d, k, h)

  toBS = pack . toList . fmap BV.unpack . Vec.unconcatBitVector# @_ @8
       . bitCoerce

  hDigest = case Hash.digestFromByteString @Hash.SHA256 $ toBS h of
    Nothing → error "The Digest should always derivable from the ByteString"
    Just x  → x

  scalarK = throwCryptoError $ decodeScalar  @Curve_P256R1 Proxy $ toBS k
  scalarD = throwCryptoError $ decodePrivate @Curve_P256R1 Proxy $ toBS d

  eq = pack
     $ toList
     $ bitCoerce @_ @(ByteVec (ByteSize (Unsigned 256) * ResultCount SignHashTest))
     $ bimap (fromInteger @(Unsigned 256)) (fromInteger @(Unsigned 256))
     $ swap
     $ fromMaybe (error "Crypton actions should not fail")
     $ fmap (signatureToIntegers Proxy)
     $ signDigestWith @Curve_P256R1 Proxy scalarK scalarD hDigest

runHitltDerivePublicKey ∷
  (ArgCount DerivePublicKeyTest ~ 1, ResultCount DerivePublicKeyTest ~ 2) ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  Unsigned 256 →
  PropertyT IO ()
runHitltDerivePublicKey sem dev settings d =
  runHitlt (type (ByteSize (Unsigned 256) * ResultCount DerivePublicKeyTest))
           sem dev settings bs eq
 where
  bs = pack $ toList
     $ bitCoerce @_
        @(ByteVec (ByteSize (Unsigned 256) * ArgCount DerivePublicKeyTest)) d

  scalarD = throwCryptoError $ decodePrivate @Curve_P256R1 Proxy bs

  eq = BS.tail
     $ encodePublic @Curve_P256R1 @ByteString Proxy
     $ toPublic @Curve_P256R1 Proxy scalarD

runStack ∷
  ∀ messageSize → KnownNat messageSize ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  [StackAction StackSize (Unsigned StackValueSize)] →
  PropertyT IO ()
runStack messageSize sem dev settings actions = do
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
      boardResponses = map (snd . bitCoerce @_ @(Unsigned StackPadding, _)
       . fromMaybe (error "unthinkable") . Vec.fromList . unpack) dutResponses

  boardResponses === safeTail (safeTail simResponses)
 where
  bsAction
    = pack
    . toList
    . bitCoerce
    . fmap (\b → if hasUndefined b then 0 else b)
    . bitCoerce @_ @(Vec _ Bit)

  safeTail = maybe (error "unthinkable") snd . List.uncons

runHitltInverseModulo ∷
  QSem →
  FilePath →
  SerialPortSettings →
  PrimeField SecP256ModPrime →
  PropertyT IO ()
runHitltInverseModulo sem dev settings x = do
  runHitlt (ByteSize (PrimeField SecP256ModPrime)) sem dev settings (toBS x)
    $ toBS $ invMod @SecP256ModPrime x
 where
  toBS
    = pack
    . toList
    . bitCoerce @_ @(ByteVec (ByteSize (PrimeField SecP256ModPrime)))

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
  PrimeField SecP256ModPrime →
  PrimeField SecP256ModPrime →
  PropertyT IO ()
runHitltKaratsubaModulo sem dev settings x y =
  runHitlt (ByteSize (PrimeField SecP256ModPrime)) sem dev settings bs eq
 where
  bs = pack $ toList
     $ bitCoerce
         @_
         @(ByteVec (2 * (ByteSize (PrimeField SecP256ModPrime)))) (x, y)

  eq = pack $ toList
     $ bitCoerce
         @_
         @(ByteVec (ByteSize (PrimeField SecP256ModPrime))) $ x * y

runHitltSHA ∷
  ∀ (alg ∷ SHA) →
  (KnownSHA alg, CryptoHash alg, Hash.HashAlgorithm (CryptoToHash alg)) ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  ByteString →
  PropertyT IO ()
runHitltSHA alg sem dev settings input
  | SHAFacts ← knownSHA alg
  , SNat ∷ SNat resultSize ← SNat @(MessageDigestSize alg `Div` 8)
  = runHitlt resultSize sem dev settings bs eq
 where
  bs = escapeAndTerminate input
  eq = cryptoHash alg input

runHitltDeterministicNonce ∷
  ∀ (alg ∷ SHA) →
  (KnownSHA alg, CryptoHash alg, Hash.HashAlgorithm (CryptoToHash alg)) ⇒
  QSem →
  FilePath →
  SerialPortSettings →
  ByteString →
  Integer →
  PropertyT IO ()
runHitltDeterministicNonce alg sem dev settings message pk
  | SHAFacts ← knownSHA alg
  , SNat ∷ SNat resultSize ← SNat @(MessageDigestSize alg `Div` 8)
  = runHitlt resultSize sem dev settings (escapeAndTerminate $ p `append` h) ref
 where
  refDig = cryptoHash# (Proxy @alg) message
  h = pack $ Memory.unpack refDig
  p = pack $ Vec.toList $ bitCoerce
    $ fromInteger @(Unsigned (MessageDigestSize SHA256)) pk
  pKref = Spec.PrivateKey (Spec.getCurveByName Spec.SEC_p256r1) pk
  ref ∷ ByteString
  ref | SHAFacts ← knownSHA alg
      , Rewrite  ← using @(CancelMultiple (MessageDigestSize alg) 8)
      = Spec.deterministicNonce Hash.SHA256 pKref refDig $ Just
      . pack . toList . bitCoerce . fromInteger @(Digest alg)

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
  , SNat ∷ SNat resultSize ← SNat @(MessageDigestSize alg `Div` 8)
  = runHitlt resultSize sem dev settings bs eq
 where
  n | SHAFacts ← knownSHA alg = natToNum @(BlockSize alg `Div` 8)
  bs = withKeySize (BS.length key)
    <> escape key
    <> escape (BS.replicate (n - BS.length key) 0xFF)
    <> escapeAndTerminate msg
  eq = BS.pack $ Memory.unpack
     $ HMAC.hmacGetDigest $ HMAC.hmac @_ @_ @(CryptoToHash alg) key msg

  withKeySize m
    | m > 0x00 && m < 0xFF = BS.pack [ 0x00, toEnum m ]
    | otherwise            = error $ "Invalid key size: " <> show m

upload ∷
  QSem →
  FilePath →
  SerialPortSettings →
  String →
  IO()
upload sem dev settings name
  = bracket_ (waitQSem sem) (signalQSem sem)
  $ hWithSerial dev settings $ \serial → do
      hSetBuffering serial NoBuffering
      -- upload the bitstream
      nixRun (".#hitlt." <> name <> ".upload")
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
  dutResponse ← liftIO
    $ bracket_ (waitQSem sem) (signalQSem sem)
    $ sendRequest messageSize dev settings bs

  pr dutResponse === pr eq
 where
  pr = concatMap (printf "%02x " ∷ Word8 → String) . unpack

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

genMod ∷ ∀ p m. (Monad m, KnownNat p, 3 ≤ p) ⇒ PropertyT m (ℤₘ p)
genMod = genModBounded minBound maxBound

genModBounded ∷ ∀ p m. (Monad m, KnownNat p, 3 ≤ p) ⇒
  Index p → Index p → PropertyT m (ℤₘ p)
genModBounded minB maxB = do
  x ← forAll $ genIndex @p $ Range.linear minB maxB
  return $ createMod @p x

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
  str      → error $ "Invalid baud: " <> str

newtype HitltTimeout = HitltTimeout String
instance Show HitltTimeout where show (HitltTimeout msg) = msg
instance Exception HitltTimeout

type ByteVec n = Vec n Word8
