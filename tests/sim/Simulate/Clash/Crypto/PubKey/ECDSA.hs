{-|
Module      : Simulate.Clash.Crypto.PubKey.ECDSA
Copyright   : Copyright © 2025-2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Simulation tests for 'Clash.Crypto.PubKey.ECDSA'.
-}

{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Simulate.Clash.Crypto.PubKey.ECDSA (tastyTests) where

import Prelude (even)
import Clash.Prelude.Safe

import Clash.Crypto.PubKey.ECDSA

import Test.Tasty
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit
import Test.Clash.Crypto.Calculator.Simulate
import Test.Clash.Crypto.PubKey.ECDSA.Simulate hiding (IsZero)

import Clash.Crypto.Calculator.Modulo (PrimeField)
import Data.Maybe (fromMaybe)
import Data.Functor.Identity (Identity(..))
import Hedgehog
import Crypto.PubKey.ECDSA (signDigestWith, decodePrivate, signatureToIntegers)
import Crypto.ECC (Curve_P256R1, EllipticCurve (..))
import Data.Data (Proxy(..))
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import qualified Hedgehog.Range as Range
import qualified Data.ByteString as BS
import qualified Crypto.Hash as Hash
import Crypto.Error (throwCryptoError)
import Crypto.PubKey.ECC.P256
import qualified Hedgehog.Gen as Gen

tastyTests ∷ TestTree
tastyTests = localOption (HedgehogTestLimit (Just 100))
  $ testGroup "Clash.Crypto.PubKey.ECDSA"
  [ testCase "SignHash (symbolically)" $ runIdentity
      ( traceM
          (SignHash ∷ Routine Nat Nat SECP256R1)
          (const $ pure ())
          (simplifyFixChoice simp)
          [Hash, Nonce, PrivKey]
      ) @?= Just [R, S]
  , testProperty "SignHash (against crypton)" $ property $ do
      uHash ← forAll $ genUnsigned $ Range.linear 0
        $ maxBound @(Unsigned 256)
      k ← forAll $ genUnsigned $ Range.linear 1
        $ bitCoerce @(PrimeField (N SECP256R1)) @CurveNum maxBound
      pKey ← forAll $ genUnsigned $ Range.linear 1
        $ bitCoerce @(PrimeField (Q SECP256R1)) @CurveNum maxBound
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
  , testProperty "Point Addition (against crypton)" $ property $ do
      p1 ← genPoint
      p2 ← genPoint
      let (x1, y1) = pointToIntegers p1
          (x2, y2) = pointToIntegers p2
          ref  = pointToIntegers $ pointAdd p1 p2
          impl = pointFromList
               $ fromMaybe (error "Routines in tests should always return")
               $ runPointAdd $ fromInteger <$> [x1,y1,x2,y2]
      ref === impl
  , testProperty "Point Addition (first is infinity)" $ property $ do
      p1 ← genPoint

      let (x1, y1) = pointToIntegers p1
          (x2, y2) = (0,0)
          ref  = (x1,y1)
          impl = pointFromList
               $ fromMaybe (error "Routines in tests should always return")
               $ runPointAdd $ fromInteger <$> [x2,y2,x1,y1]
      ref === impl
  , testProperty "Point Addition (second is infinity)" $ property $ do
      p1 ← genPoint
      let (x1, y1) = pointToIntegers p1
          (x2, y2) = (0,0)
          ref  = (x1,y1)
          impl = pointFromList
               $ fromMaybe (error "Routines in tests should always return")
               $ runPointAdd $ fromInteger <$> [x1,y1,x2,y2]
      ref === impl
  , testProperty "Point Multiplication (against crypton)" $ property $ do
      p1 ← genPoint
      s ← forAll $ genUnsigned $ Range.linear 0
        $ bitCoerce @(PrimeField (Q SECP256R1)) @CurveNum maxBound
      let (x, y) = pointToIntegers p1
          scal = throwCryptoError $ scalarFromInteger $ toInteger s
          ref  = pointToIntegers $ pointMul scal p1
          impl = pointFromList
               $ fromMaybe (error "Routines in tests should always return")
               $ runPointMul $ bitCoerce <$> [fromInteger x, fromInteger y,s]
      ref === impl
  , testProperty "IsZero" $ property $ do
      x ← forAll $ genUnsigned $ Range.linear 0
        $ bitCoerce @(PrimeField (Q SECP256R1)) @CurveNum maxBound
      let res = resultFromList
              $ fromMaybe (error "Routines in tests should always return")
              $ runIsZero [bitCoerce x]
      lsb res === bitCoerce (x == 0)
  ]

type CurveNum = Unsigned 256

genPoint ∷ Monad m ⇒ PropertyT m Crypto.PubKey.ECC.P256.Point
genPoint = do
  coeff ← forAll $ Gen.integral $ Range.linear 1
        $ 1 + toInteger @(PrimeField (Q SECP256R1)) maxBound
  return $ toPoint $ throwCryptoError $ scalarFromInteger coeff

pointFromList ∷ [CurveNum] → (Integer, Integer)
pointFromList (x:y:_) = (toInteger x, toInteger y)
pointFromList _ =
 error "Calculator should always return a list with at least two elements."

resultFromList ∷ [CurveNum] → CurveNum
resultFromList (x:_) = x
resultFromList _ =
 error "Calculator should always return a list with at least two elements."

runSignHash ∷ [CurveNum] → Maybe [CurveNum]
runSignHash = run (SignHash ∷ Routine Nat Nat SECP256R1)

runPointAdd ∷ [CurveNum] → Maybe [CurveNum]
runPointAdd = run (PointAddMain ∷ Routine Nat Nat SECP256R1)

runPointMul ∷ [CurveNum] → Maybe [CurveNum]
runPointMul = run (PointScalarMul ∷ Routine Nat Nat SECP256R1)

runIsZero ∷ [CurveNum] → Maybe [CurveNum]
runIsZero = run (IsZero ∷ Routine Nat Nat SECP256R1)

instance CalculatorNum (Unsigned 256) where
  add p x y
   | p - x > y = x + y
   | otherwise = y - (p - x)
  sub p x y
   | x >= y    = x - y
   | otherwise = p - (y - x)
  mul p x y = truncateB $ bigR `mod` extend p
   where
    bigR ∷ Unsigned 512
    bigR = extend x * extend y
  inv p a b =
   if a == 0 then b
   else moduloPower p (p - 2) a 1
  bit a j
   | j < 256, testBit a (fromEnum j) = 1
   | otherwise = 0

moduloPower ∷
  ∀ p. KnownNat p ⇒
  Unsigned p →
  Unsigned p →
  Unsigned p →
  Unsigned p →
  Unsigned p
moduloPower _ 0 _   _   = 1
moduloPower p 1 val tmp = truncateB $ r `mod` extend p
 where
  r ∷ Unsigned (p * 2)
  r = extend val * extend tmp
moduloPower p n val tmp =
 if even n then
  moduloPower p (n `div` 2) (truncateB $ r1 `mod` extend p) (tmp `mod` p)
 else
  moduloPower p (n - 1) val (truncateB $ r2 `mod` extend p)
 where
  r1, r2 ∷ Unsigned (p * 2)
  r1 = extend val * extend val
  r2 = extend tmp * extend val
