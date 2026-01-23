{-|
Module      : Simulate.Clash.Crypto.Calculator.Modulo
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Simulation tests for 'Clash.Crypto.Calculator.Modulo'.
-}

module Simulate.Clash.Crypto.Calculator.Modulo (tastyTests) where

import Clash.Crypto.Calculator.Modulo (computeModuloUnsigned, ModSize, unMod)
import Clash.Prelude.Safe
import Clash.Signal.Channel
import Data.Maybe (fromMaybe)
import Data.Monoid (First(..))
import Data.Proxy
import Data.Type.Equality (type (:~:)(Refl))
import Language.Haskell.Unicode (type (≤))
import GHC.Stack (HasCallStack)
import GHC.TypeLits.Compare ((%<=?), type (:<=?) (..))

import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import Hedgehog ((===), property, forAll, MonadTest)
import Test.Tasty
import Test.Tasty.Hedgehog (HedgehogTestLimit(HedgehogTestLimit), testProperty)

import qualified Data.List as List
import qualified Hedgehog.Range as Range

tastyTests ∷ HasCallStack ⇒ TestTree
tastyTests
  = localOption (HedgehogTestLimit (Just 100))
  $ testGroup "Clash.Crypto.Calculator.Modulo"
      [ testProperty "Equality between sequential and combinational"
        $ property $ do
          n ← forAll $ genUnsigned $ Range.linear 0 (50_000 ∷ Unsigned 64)
          modulus ← forAll $ genUnsigned $ Range.linear 2 500
          testMod n modulus
      ]

testOutput ∷
  ∀ (modT ∷ Nat) → (KnownNat modT, 1 ≤ modT, ModSize modT ≤ 64) ⇒
  Unsigned 64 →
  -- ^ n
  Unsigned 64 →
  -- ^ Modulus
  Unsigned 64
testOutput modT n modulus
  = fromMaybe (error "The returned list was empty")
  $ getFirst
  $ foldMap First
  $ sampleN @System (fromEnum (n `div` modulus) + 100)
  $ withClockResetEnable clockGen resetGen enableGen
  $ newsfeed
  $ fmap (resize . bitCoerce . unMod)
  $ computeModuloUnsigned @modT
  $ channel
  $ fmap (n, )
  $ fromList
  $ Keep : Keep : Release : List.repeat Keep

testMod ∷ (MonadFail m, MonadTest m) ⇒ Unsigned 64 → Unsigned 64 → m ()
testMod n modulus = do
  Just (SomeNat (_ ∷ Proxy modT)) ← return $ someNatVal $ toInteger modulus
  case (Proxy ∷ Proxy 1) %<=? (Proxy ∷ Proxy modT) of
    LE Refl → case (Proxy ∷ Proxy (ModSize modT)) %<=? (Proxy ∷ Proxy 64) of
      LE Refl → testOutput modT n modulus === fromIntegral n `mod` modulus
      NLE _ _ → error "ModSize modulus should be less than or equal to 64"
    NLE _ _ → error "The given modulus should be greater than 1"
