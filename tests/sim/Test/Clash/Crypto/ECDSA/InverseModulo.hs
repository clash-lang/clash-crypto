{-# OPTIONS_GHC -Wno-orphans #-}
{-|
Module      : Test.Clash.Crypto.ECDSA.InverseModulo
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.ECDSA.InverseModulo'.
-}

module Test.Clash.Crypto.ECDSA.InverseModulo (tastyTests) where

import Clash.Crypto.ECDSA.InverseModulo
  (bea, fastGcdSequential, fltCtmi, sictMiSequential, deriveSictPrecomp)
import Clash.Crypto.ECDSA.Modulo
import Clash.Prelude hiding (Mod)
import Clash.Signal.Channel
import Data.Maybe (fromMaybe)
import Data.Monoid (First(..))

import Clash.Hedgehog.Sized.Index (genIndex)
import Hedgehog
import Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog

import qualified Data.List as List
import qualified Data.Modular as Modular

-- TODO: Once all PRs are merged, move this to one place.
type Q = 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

deriveSictPrecomp @Q

tastyTests :: TestTree
tastyTests = testGroup "Clash.Crypto.ECDSA.InverseModulo"
  [ -- localOption (HedgehogTestLimit (Just 1000)) $
    --   testProperty "Functional equality of BEA" $ invModuloProperty bea,
    -- localOption (HedgehogTestLimit (Just 100)) $
    --   testProperty "Functional equality of FastGCD" $ invModuloProperty fastGcdSequential,
    localOption (HedgehogTestLimit (Just 10)) $
      testProperty "Functional equality of FLT-CTMI" $ invModuloProperty fltCtmi,
    localOption (HedgehogTestLimit (Just 100)) $
      testProperty "Functional equality of SICT-MI" $ invModuloProperty sictMiSequential]

type InvModuloComponent m dom =
 HiddenClockResetEnable dom =>
 Channel dom (Mod m) ->
 Channel dom (Mod m)

invModuloProperty :: KnownDomain System => InvModuloComponent Q System -> Property
invModuloProperty invModComp = property $ do
  f <- forAll $ genIndex $ Range.constantFrom 1 1 (maxBound - 1)
  let f' = unMod $ compute $ createMod f
  -- We can't use `Index` directly because the `inv` implementation makes it
  -- go out of bounds.
  f' === fromInteger (Modular.unMod $ fromMaybe moduloError $ Modular.inv $
                      Modular.toMod @Q $ toInteger f)
 where
  moduloError =
    error "Since the modulo of the field is prime, the inverse always exists."
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
