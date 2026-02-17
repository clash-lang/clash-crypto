{-|
Module      : Simulate.Clash.Crypto.Calculator
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Simulation tests for 'Clash.Crypto.Calculator'.
-}

module Simulate.Clash.Crypto.Calculator (tastyTests) where

import Clash.Prelude.Safe
import Clash.Hedgehog.Sized.Index (genIndex)
import Clash.Signal.Channel
import Language.Haskell.Unicode (type (≤))

import Data.Maybe (fromMaybe)
import Data.Monoid (First(..))
import Data.Kind (Type)
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog

import qualified Data.List as List
import qualified Hedgehog.Range as Range

import Clash.Crypto.Calculator
import Clash.Crypto.Calculator.ISA
import Clash.Crypto.Calculator.Modulo

import Test.Clash.Crypto.Calculator

tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.Calculator"
  [ testProperty "Calculator" $ property $ do
      a ∷ PrimeField SecP256ModPrime ← genMod
      b ∷ PrimeField SecP256ModPrime ← genMod
      testCalculator Main TestIP (bitCoerce a) (bitCoerce b)
        $ bitCoerce $ goldenRoutine a b
  ]
 where
  genMod ∷ ∀ p m. (Monad m, KnownNat p, 3 ≤ p) ⇒ PropertyT m (ℤₘ p)
  genMod = do
    x ← forAll $ genIndex @p $ Range.linear minBound maxBound
    return $ createMod @p x

testCalculator ∷
  ∀ (m ∷ Type → Type). Monad m ⇒
  ∀ {group}.
  ∀ (main ∷ group) → KnownRoutine main ⇒
  ∀ (ptr ∷ Type) → (InstructionPointer main ptr, NFDataX ptr) ⇒
  (ArgCount main ~ 2, ResultCount main ~ 1) ⇒
  Unsigned (ModSize SecP256ModPrime) →
  Unsigned (ModSize SecP256ModPrime) →
  Unsigned (ModSize SecP256ModPrime) →
  PropertyT m ()
testCalculator main ip a b c
  = (c ===)
  $ head
  $ fromMaybe (error "The returned list was empty.")
  $ getFirst
  $ foldMap First
  $ sampleN @System 1000000
  $ withClockResetEnable clockGen resetGen enableGen
  $ newsfeed
  $ calculator main ip 4 36
  $ channel
  $ fmap (a :> b :> Nil, )
  $ fromList
  $ Keep : Keep : Release : List.repeat Keep
