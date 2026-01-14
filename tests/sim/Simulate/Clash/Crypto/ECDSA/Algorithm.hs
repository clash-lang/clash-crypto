{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Simulate.Clash.Crypto.ECDSA.Algorithm (tastyTests) where

import Clash.Crypto.ECDSA.Algorithm

import Test.Tasty
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit
import Clash.Prelude hiding (Mod)
import Clash.Crypto.Calculator.Simulate
import Clash.Crypto.ECDSA.Simulate hiding (IsZero)

import qualified Data.Modular as Modular
import Clash.Crypto.Calculator.Modulo (Mod, ModSize)
import Data.Maybe (fromMaybe)
import Data.Functor.Identity (Identity(..))
import Hedgehog
import Control.DeepSeq (NFData)
import Crypto.PubKey.ECDSA (signDigestWith, decodePrivate, signatureToIntegers)
import Crypto.ECC (Curve_P256R1, EllipticCurve (..))
import Data.Data (Proxy(..))
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import qualified Hedgehog.Range as Range
import qualified Data.ByteString as BS
import qualified Crypto.Hash as Hash
import Crypto.Error (throwCryptoError)
import Crypto.PubKey.ECC.P256
import Data.Bifunctor (Bifunctor(..))
import qualified Hedgehog.Gen as Gen

tastyTests :: TestTree
tastyTests = localOption (HedgehogTestLimit (Just 100)) $
  testGroup "Clash.Crypto.ECDSA.Algorithm"
  [ testCase "Test SignHash Symbolically" $
      runIdentity
        (traceM
          (SignHash ∷ Routine Nat Nat SECP256R1)
          (const $ pure ())
          (simplifyFixChoice simp)
          [Hash, Nonce, PrivKey])
      @?= Just [R, S]
    ,
    testProperty "Test SignHash against crypton" $ property $ do
    uHash <- forAll $ genUnsigned $ Range.linear 0 (maxBound :: Unsigned 256)
    k     <- forAll $ genUnsigned
     $ Range.linear 1 (bitCoerce $ (maxBound :: Mod N') :: Unsigned 256)
    pKey  <- forAll $ genUnsigned
     $ Range.linear 1 (bitCoerce $ (maxBound :: Mod Q') :: Unsigned 256)
    let bsHash = BS.pack $ toList
               $ unpack <$> unconcatBitVector# @_ @8 (bitCoerce uHash)
        bsDigest = fromMaybe
         (error "The Digest should be always computable from the ByteString")
         $ Hash.digestFromByteString @Hash.SHA256 bsHash
        bsK = BS.pack $ toList
            $ unpack <$> unconcatBitVector# @_ @8 (bitCoerce k)
        scalarK = throwCryptoError $ decodeScalar @Curve_P256R1 Proxy bsK
        bsKey =  BS.pack $ toList
         $ unpack <$> unconcatBitVector# @_ @8 (bitCoerce pKey)
        scalarKey = throwCryptoError $ decodePrivate @Curve_P256R1 Proxy bsKey
        ref = signatureToIntegers Proxy
          <$> signDigestWith @Curve_P256R1 Proxy scalarK scalarKey bsDigest
        impl = pointFromList <$> runSignHash (bitCoerce <$> [uHash, k, pKey])
    ref === impl
    ,
    -- This test sometimes fails because of a bug in `crypton`. It tends to fail
    -- when one of the points is O.
    testProperty "Test point addition" $ property $ do
    coeff1 <- forAll $ Gen.integral
     $ Range.linear 1 (1 + (toInteger $ (maxBound :: Mod Q') :: Integer))
    coeff2 <- forAll $ Gen.integral
     $ Range.linear 1 (1 + (toInteger $ (maxBound :: Mod Q') :: Integer))
    let p1   = toPoint (throwCryptoError $ scalarFromInteger coeff1)
        p2   = toPoint (throwCryptoError $ scalarFromInteger coeff2)
        (x1, y1) = pointToIntegers p1
        (x2, y2) = pointToIntegers p2
        ref  = pointToIntegers $ pointAdd p1 p2
        impl = pointFromList
             $ fromMaybe (error "Routines in tests should always return")
             $ runPointAdd $ fromInteger <$> [x1,y1,x2,y2]
    ref === impl
    ,
    testProperty "Test point addition (first is infinity)" $ property $ do
    coeff <- forAll $ Gen.integral
     $ Range.linear 1 (1 + (toInteger $ (maxBound :: Mod Q') :: Integer))
    let p1   = toPoint (throwCryptoError $ scalarFromInteger coeff)
        (x1, y1) = pointToIntegers p1
        (x2, y2) = (0,0)
        ref  = (x1,y1)
        impl = pointFromList
             $ fromMaybe (error "Routines in tests should always return")
             $ runPointAdd $ fromInteger <$> [x2,y2,x1,y1]
    ref === impl
    ,
    testProperty "Test point addition (second is infinity)" $ property $ do
    coeff <- forAll $ Gen.integral
     $ Range.linear 1 (1 + (toInteger $ (maxBound :: Mod Q') :: Integer))
    let p1   = toPoint (throwCryptoError $ scalarFromInteger coeff)
        (x1, y1) = pointToIntegers p1
        (x2, y2) = (0,0)
        ref  = (x1,y1)
        impl = pointFromList
             $ fromMaybe (error "Routines in tests should always return")
             $ runPointAdd $ fromInteger <$> [x1,y1,x2,y2]
    ref === impl
    ,
    testProperty "Test point multiplication" $ property $ do
    x <- forAll $ genUnsigned
     $ Range.linear 0 (bitCoerce $ (maxBound :: Mod Q') :: Unsigned 256)
    y <- forAll $ genUnsigned
     $ Range.linear 0 (bitCoerce $ (maxBound :: Mod Q') :: Unsigned 256)
    s <- forAll $ genUnsigned
     $ Range.linear 0 (bitCoerce $ (maxBound :: Mod Q') :: Unsigned 256)
    let xI   = toInteger x
        yI   = toInteger y
        p1   = pointFromIntegers (xI, yI)
        scal = throwCryptoError $ scalarFromInteger $ toInteger s
        ref  = pointToIntegers $ pointMul scal p1
        impl = pointFromList
             $ fromMaybe (error "Routines in tests should always return")
             $ runPointMul $ bitCoerce <$> [x,y,s]
    ref === impl
    ,
    testProperty "Test IsZero" $ property $ do
    x <- forAll $ genUnsigned
     $ Range.linear 0 (bitCoerce $ (maxBound :: Mod Q') :: Unsigned 256)
    let res = resultFromList
            $ fromMaybe (error "Routines in tests should always return")
            $ runIsZero [bitCoerce x]
    lsb res === bitCoerce (x == 0)
  ]

type CurveNum = Unsigned 256

pointFromList :: [CurveNum] -> (Integer, Integer)
pointFromList (x:y:_) = (toInteger x, toInteger y)
pointFromList _ =
 error "Calculator should always return a list with at least two elements."

resultFromList :: [CurveNum] -> CurveNum
resultFromList (x:_) = x
resultFromList _ =
 error "Calculator should always return a list with at least two elements."

runSignHash :: [CurveNum] -> Maybe [CurveNum]
runSignHash = run (SignHash :: Routine Nat Nat SECP256R1)

runPointAdd :: [CurveNum] -> Maybe [CurveNum]
runPointAdd = run (PointAddMain :: Routine Nat Nat SECP256R1)

runPointMul :: [CurveNum] -> Maybe [CurveNum]
runPointMul = run (PointScalarMul :: Routine Nat Nat SECP256R1)

runIsZero :: [CurveNum] -> Maybe [CurveNum]
runIsZero = run (IsZero :: Routine Nat Nat SECP256R1)

-- instance NFData (Mod 0xffffffff_00000001_00000000_00000000_00000000_ffffffff_ffffffff_ffffffff)

makeOp :: forall a . (KnownNat a, 1 <= a) =>
 forall b -> (KnownNat b, 1 <= b, ModSize a ~ ModSize b) =>
  (forall f. (KnownNat f, 1 <= f) => Mod f -> Mod f -> Mod f) ->
  Mod a -> Mod a -> Mod a
makeOp b op = curry $ bitCoerce . uncurry (op @b) . bimap bitCoerce bitCoerce

instance CalculatorNum (Unsigned 256) where
  add p x y
   | p - x > y = x + y
   | otherwise = y - (p - x)
  sub p x y
   | x >= y    = x - y
   | otherwise = p - (y - x)
  mul p x y = truncateB $ bigR `mod` extend p
   where
    bigR :: Unsigned 512
    bigR = extend x * extend y
  inv p a b =
   if a == 0 then b
   else moduloPower p (p - 2) a 1
  bit a j
   | j < 256, testBit a (fromEnum j) = 1
   | otherwise = 0

moduloPower :: forall p. KnownNat p =>
 Unsigned p -> Unsigned p -> Unsigned p -> Unsigned p -> Unsigned p
moduloPower p 0 _   tmp = 1
moduloPower p 1 val tmp = truncateB $ r `mod` extend p
 where
  r :: Unsigned (p * 2)
  r = extend val * extend tmp
moduloPower p n val tmp =
 if even n then
  moduloPower p (n `div` 2) (truncateB $ r1 `mod` extend p) (tmp `mod` p)
 else
  moduloPower p (n - 1) val (truncateB $ r2 `mod` extend p)
 where
  r1, r2 :: Unsigned (p * 2)
  r1 = extend val * extend val
  r2 = extend tmp * extend val
