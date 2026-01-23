{-|
Module      : Simulate.Clash.Crypto.Calculator.InverseModulo
Copyright   : Copyright © 2025-2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Simulation tests for 'Clash.Crypto.Calculator.InverseModulo'.
-}

{-# OPTIONS_GHC -freduction-depth=400 #-}

module Simulate.Clash.Crypto.Calculator.InverseModulo (tastyTests) where

import Clash.Prelude.Safe
import Clash.Signal.Channel
import Data.Maybe (fromMaybe)
import Data.Monoid (First(..))

import Clash.Hedgehog.Sized.Index (genIndex)
import Hedgehog
import Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog

import qualified Data.List as List

import Clash.Crypto.Calculator.ISA (SecP256ModPrime)
import Clash.Crypto.Calculator.InverseModulo
  (bea, fastGcdSequential, fltCtmi, sictMiSequential)
import Clash.Crypto.Calculator.Modulo

import Test.Clash.Crypto.Calculator.InverseModulo (invMod)

tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.Calculator.InverseModulo"
  [ localOption (HedgehogTestLimit (Just 1000))
  $ testProperty "BEA (functional equality)"
  $ invModuloProperty bea

  , localOption (HedgehogTestLimit (Just 100))
  $ testProperty "FastGCD (functional equality)"
  $ invModuloProperty fastGcdSequential

  , localOption (HedgehogTestLimit (Just 10))
  $ testProperty "FLT-CTMI (functional equality)"
  $ invModuloProperty fltCtmi

  , localOption (HedgehogTestLimit (Just 100))
  $ testProperty "SICT-MI (functional equality)"
  $ invModuloProperty sictMiSequential
  ]

invModuloProperty ∷
  ( HiddenClockResetEnable System ⇒
    Channel System (PrimeField SecP256ModPrime) →
    Channel System (PrimeField SecP256ModPrime)
  ) → Property
invModuloProperty invModComp = property $ do
  f0 ← forAll $ genIndex $ Range.constantFrom 1 1 (maxBound - 1)
  let f1 = createMod @SecP256ModPrime f0
  -- We can't use `Index` directly because the `inv` implementation makes it
  -- go out of bounds.
  compute f1 === invMod f1
 where
  compute input
    = fromMaybe (error "The returned list was empty")
    $ getFirst
    $ foldMap First
    $ sampleN @System 10000000
    $ withClockResetEnable @System clockGen resetGen enableGen
    $ newsfeed
    $ invModComp
    $ channel
    $ fmap (input, )
    $ fromList
    $ Keep : Keep : Release : List.repeat Keep
