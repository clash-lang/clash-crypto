{-|
Module      : Test.Clash.Crypto.ECDSA.CLU
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Calculator.CLU'.
-}

{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeAbstractions #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Clash.Crypto.Calculator.CLU where

import Clash.Prelude hiding (Mod)
import Clash.Hedgehog.Sized.Index (genIndex)
import Clash.Signal.Channel
import Language.Haskell.Unicode (type (≤))

import Data.Maybe (fromMaybe)
import Data.Monoid (First(..))
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog

import qualified Data.List as List
import qualified Data.Modular as Modular
import qualified Hedgehog.Range as Range

import Clash.Crypto.Calculator.CLU
import Clash.Crypto.ECDSA.Modulo (Mod, ModSize, createMod, unMod)

tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.ECDSA.CLU"
  [ localOption (HedgehogTestLimit (Just 500))
  $ testGroup "CLU Tests"
      [ testProperty "Addition" $ property $ do
          a ∷ CMod SecP256Mod ← genMod
          b ∷ CMod SecP256Mod ← genMod
          testCLU SecP256Mod Add a b $ a + b
          c ∷ CMod SecP256Ord ← genMod
          d ∷ CMod SecP256Ord ← genMod
          testCLU SecP256Ord Add c d $ c + d
      , testProperty "Substraction" $ property $ do
          a ∷ CMod SecP256Mod ← genMod
          b ∷ CMod SecP256Mod ← genMod
          testCLU SecP256Mod Sub a b $ a - b
          c ∷ CMod SecP256Ord ← genMod
          d ∷ CMod SecP256Ord ← genMod
          testCLU SecP256Ord Sub c d $ c - d
      , localOption (HedgehogTestLimit (Just 20))
        $ testProperty "Inverse" $ property $ do
          a ∷ CMod SecP256Mod ← genMod
          b ∷ CMod SecP256Mod ← genMod
          testCLU SecP256Mod Inv a b $ if
            | a == 0    → b
            | otherwise → invGolden a
          c ∷ CMod SecP256Ord ← genMod
          d ∷ CMod SecP256Ord ← genMod
          testCLU SecP256Ord Inv c d $ if
            | c == 0    → d
            | otherwise → invGolden c
      , testProperty "Multiplication" $ property $ do
          a ∷ CMod SecP256Mod ← genMod
          b ∷ CMod SecP256Mod ← genMod
          testCLU SecP256Mod Mul a b $ a * b
          c ∷ CMod SecP256Ord ← genMod
          d ∷ CMod SecP256Ord ← genMod
          testCLU SecP256Ord Mul c d $ c * d
      , testProperty "Test Bit" $ property $ do
          a ∷ CMod SecP256Mod ← genMod
          b ∷ CMod SecP256Mod ← genMod
          testCLU SecP256Mod Bit a b $ if
            | b < natToNum @(ModSize (CPrime SecP256Mod))
            , testBit a (fromEnum b) → 1
            | otherwise → 0
          c ∷ CMod SecP256Ord ← genMod
          d ∷ CMod SecP256Ord ← genMod
          testCLU SecP256Ord Bit c d $ if
            | d < natToNum @(ModSize (CPrime SecP256Ord))
            , testBit c (fromEnum d) → 1
            | otherwise → 0
      ]
  ]
 where
  genMod ∷ ∀ p m. (Monad m, KnownNat p, 3 ≤ p) ⇒ PropertyT m (Mod p)
  genMod = do
    x ← forAll $ genIndex @p $ Range.linear minBound maxBound
    return $ createMod @p x

testCLU ∷ ∀ p m. (Monad m, KnownNat p, 3 ≤ p, p ≤ CPrime SecP256Mod) ⇒
  ECPrime →
  CluInstruction →
  Mod p →
  Mod p →
  Mod p →
  PropertyT m ()
testCLU p op a b c
  = (ex c ===)
  $ fromMaybe (error "The returned list was empty")
  $ getFirst
  $ foldMap First
  $ sampleN @System 1000000
  $ withClockResetEnable clockGen resetGen enableGen
  $ newsfeed
  $ clu d4 d36
  $ channel
  $ fmap ((p, (op, (ex a, ex b))), )
  $ fromList
  $ Keep : Keep : Release : List.repeat Keep
 where
  ex ∷ Mod p → CMod SecP256Mod
  ex = createMod . extend @_ @_ @(CPrime SecP256Mod - p) . unMod

invGolden ∷ ∀ p. Modular.Modulus p ⇒ Mod p → Mod p
invGolden
  = fromInteger
  . Modular.unMod
  . fromMaybe moduloError
  . Modular.inv
  . Modular.toMod @p
  . toInteger
 where
  moduloError =
    error "Since the modulo of the field is prime, the inverse always exists."
