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
import Crypto.PubKey.ECDSA (signDigestWith, decodePrivate, signatureToIntegers, toPublic, encodePublic)
import Crypto.ECC (Curve_P256R1, EllipticCurve (..))
import Data.Data (Proxy(..))
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import qualified Hedgehog.Range as Range
import qualified Data.ByteString as BS
import qualified Crypto.Hash as Hash
import Crypto.Error (throwCryptoError)
import Crypto.PubKey.ECC.P256
import qualified Hedgehog.Gen as Gen
import Data.Word (Word8)

tastyTests ∷ TestTree
tastyTests = localOption (HedgehogTestLimit (Just 100))
  $ testGroup "Clash.Crypto.PubKey.ECDSA"
  [ testGroup "SignHash"
    [ testCase "symbolically" $ runIdentity
        ( traceM
            (SignHash ∷ Routine Nat Nat SECP256R1)
            (const $ pure ())
            (simplifyFixChoice simp)
            [Hash, Nonce, PrivKey]
        ) @?= Just [R, S]
    , testProperty "against crypton" $ property $ do
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
    ]
  , testGroup "PointAdd"
    [ testProperty "against crypton" $ property $ do
        p1 ← genPoint
        p2 ← genPoint
        let (x1, y1) = pointToIntegers p1
            (x2, y2) = pointToIntegers p2
            ref  = pointToIntegers $ pointAdd p1 p2
            impl = pointFromList
                 $ fromMaybe (error "Routines in tests should always return")
                 $ runPointAdd $ fromInteger <$> [x1,y1,x2,y2]
        ref === impl
    , testProperty "first is infinity" $ property $ do
        p1 ← genPoint

        let (x1, y1) = pointToIntegers p1
            (x2, y2) = (0,0)
            ref  = (x1,y1)
            impl = pointFromList
                 $ fromMaybe (error "Routines in tests should always return")
                 $ runPointAdd $ fromInteger <$> [x2,y2,x1,y1]
        ref === impl
    , testProperty "second is infinity" $ property $ do
        p1 ← genPoint
        let (x1, y1) = pointToIntegers p1
            (x2, y2) = (0,0)
            ref  = (x1,y1)
            impl = pointFromList
                 $ fromMaybe (error "Routines in tests should always return")
                 $ runPointAdd $ fromInteger <$> [x1,y1,x2,y2]
        ref === impl
    ]
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
  , testProperty "DerivePublicKey" $ property $ do
      pKey ← forAll $ genUnsigned $ Range.linear 1
        $ bitCoerce @(PrimeField (Q SECP256R1)) @CurveNum maxBound

      let bsKey = BS.pack $ toList
            $ unpack <$> unconcatBitVector# @_ @8 (bitCoerce pKey)
          scalarKey = throwCryptoError $ decodePrivate @Curve_P256R1 Proxy bsKey
          scalarPubKey = toPublic (Proxy @Curve_P256R1) scalarKey
          ref =
           BS.tail $ encodePublic @Curve_P256R1 @BS.ByteString Proxy scalarPubKey
          impl = BS.pack $ toList $ bitCoerce @(CurveNum, CurveNum) @(Vec _ Word8)
               $ pointFromList
               $ fromMaybe (error "Routines in tests should always return")
               $ runDerivePublicKey [pKey]
      ref === impl
  ]

type CurveNum = Unsigned 256

genPoint ∷ Monad m ⇒ PropertyT m Crypto.PubKey.ECC.P256.Point
genPoint = do
  coeff ← forAll $ Gen.integral $ Range.linear 1
        $ 1 + toInteger @(PrimeField (Q SECP256R1)) maxBound
  return $ toPoint $ throwCryptoError $ scalarFromInteger coeff

pointFromList ∷ Num a ⇒ [CurveNum] → (a, a)
pointFromList (x:y:_) = (fromIntegral x, fromIntegral y)
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

runDerivePublicKey ∷ [CurveNum] → Maybe [CurveNum]
runDerivePublicKey = run (DerivePublicKey ∷ Routine Nat Nat SECP256R1)
