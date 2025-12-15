{-# LANGUAGE MagicHash #-}
module Simulate.Clash.Crypto.ECDSA.Algorithm where

import Clash.Crypto.ECDSA.Algorithm

import Test.Tasty
import Test.Tasty.Hedgehog
import Clash.Prelude hiding (Mod)
import Clash.Crypto.Calculator.Simulate

import qualified Data.Modular as Modular
import Clash.Crypto.Calculator.Modulo (Mod)
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

tastyTests :: TestTree
tastyTests = localOption (HedgehogTestLimit (Just 100)) $
  testGroup "Clash.Crypto.ECDSA.Algorithm"
  [
    testProperty "Test SignHash against crypton" $ property $ do
    uHash <- forAll $ genUnsigned $ Range.linear 1 (maxBound :: Unsigned 256)
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
        impl = pointFromList <$> runSignHash (bitCoerce <$> [uHash, pKey, k])
    ref === impl
    ,
    testProperty "Test point addition" $ property $ do
    x1 <- forAll $ genUnsigned
     $ Range.linear 0 (bitCoerce $ (maxBound :: Mod Q') :: Unsigned 256)
    y1 <- forAll $ genUnsigned
     $ Range.linear 0 (bitCoerce $ (maxBound :: Mod Q') :: Unsigned 256)
    x2 <- forAll $ genUnsigned
     $ Range.linear 0 (bitCoerce $ (maxBound :: Mod Q') :: Unsigned 256)
    y2 <- forAll $ genUnsigned
     $ Range.linear 0 (bitCoerce $ (maxBound :: Mod Q') :: Unsigned 256)
    let xI1  = toInteger x1
        yI1  = toInteger y1
        xI2  = toInteger x2
        yI2  = toInteger y2
        p1   = pointFromIntegers (xI1, yI1)
        p2   = pointFromIntegers (xI2, yI2)
        ref  = pointToIntegers $ pointAdd p1 p2
        impl = pointFromList
             $ fromMaybe (error "Routines in tests should always return")
             $ runPointAdd $ bitCoerce <$> [x1,y1,x2,y2]
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
             $ runPointAdd $ bitCoerce <$> [x,y,s]
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

invMod :: forall a. (KnownNat a, 1 <= a) => Mod a -> Integer
invMod
  = Modular.unMod
  . fromMaybe (error "The inverse always exists in a prime field.")
  . Modular.inv @a
  . Modular.toMod
  . toInteger

instance NFData (Mod 0xffffffff_00000001_00000000_00000000_00000000_ffffffff_ffffffff_ffffffff)

-- Weird enough
instance CalculatorNum (Mod 0xffffffff_00000001_00000000_00000000_00000000_ffffffff_ffffffff_ffffffff) where
  add = (+)
  sub = (-)
  mul = (*)
  inv a b = fromInteger $
   if b == natToNum @Q' then invMod @Q' a else invMod @N' $ bitCoerce a
  bit a = bitCoerce . resize . bitCoerce @_ @(Unsigned 1) . testBit a . fromEnum
