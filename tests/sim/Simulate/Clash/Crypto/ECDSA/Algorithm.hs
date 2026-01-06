{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Simulate.Clash.Crypto.ECDSA.Algorithm (tastyTests) where

import Clash.Crypto.ECDSA.Algorithm

import Test.Tasty
import Test.Tasty.Hedgehog
import Clash.Prelude hiding (Mod)
import Clash.Crypto.Calculator.Simulate

import qualified Data.Modular as Modular
import Clash.Crypto.Calculator.Modulo (Mod, ModSize)
import Data.Maybe (fromMaybe)
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
import Clash.Crypto.Calculator.ISA (ECPrime(..))
import Data.Bifunctor (Bifunctor(..))
import qualified Hedgehog.Gen as Gen

tastyTests :: TestTree
tastyTests = localOption (HedgehogTestLimit (Just 100)) $
  testGroup "Clash.Crypto.ECDSA.Algorithm"
  [
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

pointFromList :: [Mod Q'] -> (Integer, Integer)
pointFromList (x:y:_) = (toInteger x, toInteger y)
pointFromList _ =
 error "Calculator should always return a list with at least two elements."

resultFromList :: [Mod Q'] -> Mod Q'
resultFromList (x:_) = x
resultFromList _ =
 error "Calculator should always return a list with at least two elements."

runSignHash :: [Mod Q'] -> Maybe [Mod Q']
runSignHash = run (SignHash :: Routine Nat Nat SECP256R1)

runPointAdd :: [Mod Q'] -> Maybe [Mod Q']
runPointAdd = run (PointAdd :: Routine Nat Nat SECP256R1)

runPointMul :: [Mod Q'] -> Maybe [Mod Q']
runPointMul = run (PointScalarMul :: Routine Nat Nat SECP256R1)

runIsZero :: [Mod Q'] -> Maybe [Mod Q']
runIsZero = run (IsZero :: Routine Nat Nat SECP256R1)

invMod :: forall a -> (KnownNat a, 1 <= a) => Mod a -> Mod a
invMod a
  = fromInteger
  . Modular.unMod
  . fromMaybe (error "The inverse always exists in a prime field.")
  . Modular.inv @a
  . Modular.toMod
  . toInteger

instance NFData (Mod 0xffffffff_00000001_00000000_00000000_00000000_ffffffff_ffffffff_ffffffff)

makeOp :: forall a . (KnownNat a, 1 <= a) =>
 forall b -> (KnownNat b, 1 <= b, ModSize a ~ ModSize b) =>
  (forall f. (KnownNat f, 1 <= f) => Mod f -> Mod f -> Mod f) ->
  Mod a -> Mod a -> Mod a
makeOp b op = curry $ bitCoerce . uncurry (op @b) . bimap bitCoerce bitCoerce

instance CalculatorNum (Mod 0xffffffff_00000001_00000000_00000000_00000000_ffffffff_ffffffff_ffffffff) where
  add p = case p of
    SecP256Mod -> (+)
    SecP256Ord -> makeOp N' (+)
  sub p = case p of
    SecP256Mod -> (-)
    SecP256Ord -> makeOp N' (-)
  mul p = case p of
    SecP256Mod -> (*)
    SecP256Ord -> makeOp N' (*)
  inv p a b =
   if a == 0 then b else
    (case p of
     SecP256Mod -> invMod Q'
     SecP256Ord -> bitCoerce . invMod N' . bitCoerce) a
  bit a = bitCoerce . extend . bitCoerce @_ @(Unsigned 1) . testBit a . fromEnum
