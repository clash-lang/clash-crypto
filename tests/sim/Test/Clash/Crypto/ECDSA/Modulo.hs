{-# LANGUAGE AllowAmbiguousTypes #-}

{-|
Module      : Test.Clash.Crypto.ECDSA.Modulo
Copyright   : Copyright © 2024 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.ECDSA.Modulo'.
-}

module Test.Clash.Crypto.ECDSA.Modulo where

import Test.Tasty
import Test.Tasty.Hedgehog (HedgehogTestLimit(HedgehogTestLimit), testProperty)
import Clash.Prelude
import Hedgehog ((===), property, forAll)

import qualified Hedgehog.Range as Range
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import Data.Maybe (catMaybes)
import Clash.Crypto.ECDSA.Modulo (computeModuloPos, ModSize, unMod)
import GHC.Stack (HasCallStack)
import Data.Constraint (Dict (..))
import Unsafe.Coerce (unsafeCoerce)


import qualified Data.List as List
import Data.Proxy

type DenMaxTest = 200

tastyTests :: HasCallStack => TestTree
tastyTests = testGroup "Clash.Crypto.ECDSA.Modulo"
  [ localOption (HedgehogTestLimit (Just 100))
  $  testGroup "Modulo"
      [ testProperty ("Equality between streaming modulo and combinatorial modulo")
        $ property $ do
          -- TODO: Include negative numbers in test
          n <- forAll $ genUnsigned $ Range.linear 0 (50_000 :: Unsigned 64)
          modulus <- forAll $ genUnsigned $ Range.linear 2 500
          testMod n modulus
      ]
  ]

testOutput ::
  forall (modT :: Nat).
  (KnownNat modT) =>
  Unsigned 64 ->
  -- ^ n
  [Maybe (Unsigned 64)] ->
  -- ^ TestInput
  Unsigned 64 ->
  -- ^ Modulus
  Unsigned 64
testOutput n testInput modulus
 | Dict <- unsafeCoerce (Dict :: Dict (0 <= 0)) :: Dict (1 <= modT)
 , Dict <- unsafeCoerce (Dict :: Dict (0 <= 0)) :: Dict (ModSize modT <= 64)
 =
 List.head
  $ catMaybes
  $ sampleN @System (ceiling (fromIntegral (abs n) / fromIntegral modulus) + 100)
  $ withClockResetEnable clockGen resetGen enableGen
  $ fmap (fmap (resize . unMod)) $ computeModuloPos @modT (fromList testInput)

testMod n modulus = do
  Just (SomeNat (_ :: Proxy modT)) <- return $ someNatVal $ toInteger modulus
  let testInput =
        [Nothing, Nothing]
        <> [Just n]
        <> List.repeat Nothing
  testOutput @modT n testInput modulus === fromIntegral n `mod` modulus

