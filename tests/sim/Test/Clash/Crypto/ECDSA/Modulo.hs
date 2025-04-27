{-# LANGUAGE AllowAmbiguousTypes #-}

{-|
Module      : Test.Clash.Crypto.ECDSA.Modulo
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.ECDSA.Modulo'.
-}

module Test.Clash.Crypto.ECDSA.Modulo where

import Test.Tasty
import Test.Tasty.Hedgehog (HedgehogTestLimit(HedgehogTestLimit), testProperty)
import Clash.Prelude
import Hedgehog ((===), property, forAll, MonadTest)

import qualified Hedgehog.Range as Range
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import Data.Maybe (catMaybes, listToMaybe)
import Clash.Crypto.ECDSA.Modulo (computeModuloPos, ModSize, unMod)
import GHC.Stack (HasCallStack)


import qualified Data.List as List
import Data.Proxy
import GHC.TypeLits.Compare ((%<=?), type (:<=?) (..))
import Data.Type.Equality (type (:~:)(Refl))

tastyTests :: HasCallStack => TestTree
tastyTests = testGroup "Clash.Crypto.ECDSA.Modulo"
  [ localOption (HedgehogTestLimit (Just 100))
  $  testGroup "Modulo"
      [ testProperty ("Equality between sequential modulo and combinatorial modulo")
        $ property $ do
          n <- forAll $ genUnsigned $ Range.linear 0 (50_000 :: Unsigned 64)
          modulus <- forAll $ genUnsigned $ Range.linear 2 500
          testMod n modulus
      ]
  ]

testOutput ::
  forall (modT :: Nat).
  (KnownNat modT, 1 <= modT, ModSize modT <= 64) =>
  Unsigned 64 ->
  -- ^ n
  [Maybe (Unsigned 64)] ->
  -- ^ TestInput
  Unsigned 64 ->
  -- ^ Modulus
  Unsigned 64
testOutput n testInput modulus
  = let output =
          catMaybes
          $ sampleN @System (ceiling (fromIntegral (abs n) / fromIntegral modulus :: Double) + 100)
          $ withClockResetEnable clockGen resetGen enableGen
          $ fmap (fmap (resize . bitCoerce . unMod)) $ computeModuloPos @modT (fromList testInput)
  in case listToMaybe output of
        Just a -> a
        Nothing -> error "The returned list was empty"
    

testMod :: (MonadFail m, MonadTest m) => Unsigned 64 -> Unsigned 64 -> m ()
testMod n modulus = do
  Just (SomeNat (_ :: Proxy modT)) <- return $ someNatVal $ toInteger modulus
  let testInput =
        [Nothing, Nothing]
        <> [Just n]
        <> List.repeat Nothing
  case (Proxy :: Proxy 1) %<=? (Proxy :: Proxy modT) of
    LE Refl -> case (Proxy :: Proxy (ModSize modT)) %<=? (Proxy :: Proxy 64) of
      LE Refl -> testOutput @modT n testInput modulus === fromIntegral n `mod` modulus
      NLE _ _ -> error "ModSize modulus should be less than or equal to 64"
    NLE _ _ -> error "The given modulus should be greater than 1"

