{-|
Module      : Test.Clash.Crypto.ECDSA.InverseModulo
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.ECDSA.InverseModulo'.
-}

module Test.Clash.Crypto.ECDSA.InverseModulo (tastyTests) where

import Clash.Crypto.ECDSA.InverseModulo (bea, fastGcdSequential, fltCtmi)
import Clash.Crypto.ECDSA.Modulo
import Clash.Prelude hiding (Mod)
import Data.Maybe (catMaybes, listToMaybe, fromMaybe)

import Clash.Hedgehog.Sized.Index (genIndex)
import Hedgehog
import Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog

import qualified Data.List as List
import qualified Data.Modular as Modular

-- TODO: Once all PRs are merged, move this to one place.
type Q = 115792089210356248762697446949407573530086143415290314195533631308867097853951

tastyTests :: TestTree
tastyTests = testGroup "Clash.Crypto.ECDSA.InverseModulo"
  [ localOption (HedgehogTestLimit (Just 1000)) $
      testProperty "Functional equality of BEA" $ invModuloProperty bea,
    localOption (HedgehogTestLimit (Just 100)) $
      testProperty "Functional equality of FastGCD" $ invModuloProperty fastGcdSequential,
    localOption (HedgehogTestLimit (Just 10)) $
      testProperty "Functional equality of FLT-CTMI" $ invModuloProperty fltCtmi]

type InvModuloComponent m dom =
 HiddenClockResetEnable dom =>
 Signal dom Bool ->
 Signal dom (Mod m) ->
 Signal dom (Maybe (Mod m))

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
  compute input =
    let r = catMaybes $
            sampleN @System 10000000 $
            withClockResetEnable @System clockGen resetGen enableGen $
            invModComp (fromList toggleInput) (fromList $ List.repeat input)
    in case listToMaybe r of
     Just a  -> a
     Nothing -> error "The returned list was empty"

  toggleInput = [False, False] <> List.repeat True
