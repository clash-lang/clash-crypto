{-|
Module      : Simulate.Clash.Crypto.Calculator.CLU
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Simulation tests for 'Clash.Crypto.Calculator.CLU'.
-}

{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE UndecidableInstances #-}

module Simulate.Clash.Crypto.Calculator.CLU where

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

import Clash.Crypto.Calculator.ISA
import Clash.Crypto.Calculator.CLU
import Clash.Crypto.Calculator.Modulo

tastyTests ∷ TestTree
tastyTests
  = localOption (HedgehogTestLimit (Just 1000))
  $ testGroup "Clash.Crypto.Calculator.CLU"
      [ testProperty "Addition" $ property $ do
          a ∷ Mod SecP256ModPrime ← genMod
          b ∷ Mod SecP256ModPrime ← genMod
          testCLU Add a b $ a + b
          c ∷ Mod SecP256OrdPrime ← genMod
          d ∷ Mod SecP256OrdPrime ← genMod
          testCLU Add c d $ c + d
      , testProperty "Subtraction" $ property $ do
          a ∷ Mod SecP256ModPrime ← genMod
          b ∷ Mod SecP256ModPrime ← genMod
          testCLU Sub a b $ a - b
          c ∷ Mod SecP256OrdPrime ← genMod
          d ∷ Mod SecP256OrdPrime ← genMod
          testCLU Sub c d $ c - d
      , testProperty "TestBit" $ property $ do
          a ∷ Mod SecP256ModPrime ← genMod
          b ∷ Mod SecP256ModPrime ← genMod
          testCLU Bit a b $ if
            | b < natToNum @(ModSize SecP256ModPrime)
            , testBit a (fromEnum b) → 1
            | otherwise → 0
          c ∷ Mod SecP256OrdPrime ← genMod
          d ∷ Mod SecP256OrdPrime ← genMod
          testCLU Bit c d $ if
            | d < natToNum @(ModSize SecP256OrdPrime)
            , testBit c (fromEnum d) → 1
            | otherwise → 0
      , testProperty "Multiplication" $ property $ do
          a ∷ Mod SecP256ModPrime ← genMod
          b ∷ Mod SecP256ModPrime ← genMod
          testCLU Mul a b $ a * b
          c ∷ Mod SecP256OrdPrime ← genMod
          d ∷ Mod SecP256OrdPrime ← genMod
          testCLU Mul c d $ c * d
      , localOption (HedgehogTestLimit (Just 20))
        $ testProperty "Inverse" $ property $ do
          a ∷ Mod SecP256ModPrime ← genMod
          b ∷ Mod SecP256ModPrime ← genMod
          testCLU Inv a b $ if
            | a == 0    → b
            | otherwise → invGolden a
          c ∷ Mod SecP256OrdPrime ← genMod
          d ∷ Mod SecP256OrdPrime ← genMod
          testCLU Inv c d $ if
            | c == 0    → d
            | otherwise → invGolden c
      ]
 where
  genMod ∷ ∀ p m. (Monad m, KnownNat p, 3 ≤ p) ⇒ PropertyT m (Mod p)
  genMod = do
    x ← forAll $ genIndex @p $ Range.linear minBound maxBound
    return $ createMod @p x

testCLU ∷ ∀ p m. (Monad m, KnownNat p, 3 ≤ p, p ≤ SecP256ModPrime) ⇒
  CluInstruction →
  Mod p →
  Mod p →
  Mod p →
  PropertyT m ()
testCLU op a b c
  = (ex c ===)
  $ fromMaybe (error "The returned list was empty.")
  $ getFirst
  $ foldMap First
  $ sampleN @System 1000000
  $ withClockResetEnable clockGen resetGen enableGen
  $ newsfeed
  $ clu 4 36
  $ channel
  $ fmap ((op, ((ex a, ex b), natToNum @(p - 1) + 1)), )
  $ fromList
  $ Keep : Keep : Release : List.repeat Keep
 where
  ex ∷ Mod p → Unsigned (ModSize p)
  ex = bitCoerce

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
    error "The inverse always exists in a prime field."
