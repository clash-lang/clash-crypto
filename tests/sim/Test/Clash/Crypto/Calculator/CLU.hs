{-|
Module      : Test.Clash.Crypto.ECDSA.CLU
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.ECDSA.CLU'.
-}

{-# LANGUAGE MultiWayIf #-}

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
import Clash.Crypto.ECDSA.InverseModulo (deriveSictPrecomp)
import Clash.Crypto.ECDSA.Modulo (Mod, ModSize, createMod)


-- TODO: Once all PRs are merged, move this to one place.
type Q = 115792089210356248762697446949407573530086143415290314195533631308867097853951

deriveSictPrecomp @Q

tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.ECDSA.CLU"
  [ localOption (HedgehogTestLimit (Just 500))
  $ testGroup "CLU Tests"
      [ testProperty "Addition" $ property $ do
          a ← genMod
          b ← genMod
          testCLU (SNat @Q) Add a b
            $ a + b
      , testProperty "Substraction" $ property $ do
          a ← genMod
          b ← genMod
          testCLU (SNat @Q) Sub a b
            $ a - b
      , localOption (HedgehogTestLimit (Just 20))
      $ testProperty "Inverse" $ property $ do
          a ← genMod
          b ← genMod
          testCLU (SNat @Q) Inv a b $ if
            | a == 0 → b
            | otherwise
            → fromInteger
            $ Modular.unMod
            $ fromMaybe moduloError
            $ Modular.inv
            $ Modular.toMod @Q
            $ toInteger a
      , testProperty "Multiplication" $ property $ do
          a ← genMod
          b ← genMod
          testCLU (SNat @Q) Mul a b $ a * b
      , testProperty "Test Bit" $ property $ do
          a ← genMod
          b ← genMod
          testCLU (SNat @Q) Bit a b $ if
            | b < natToNum @(ModSize Q), testBit a (fromEnum b) → 1
            | otherwise → 0
      ]
  ]
 where
  genMod = do
    x ← forAll $ genIndex $ Range.linear minBound maxBound
    return $ createMod @Q x

  moduloError =
    error "Since the modulo of the field is prime, the inverse always exists."

testCLU ∷ (Monad m, 3 ≤ p) ⇒
  SNat p →
  CluInstruction →
  Mod p →
  Mod p →
  Mod p →
  PropertyT m ()
testCLU SNat op a b
  = (===)
  $ fromMaybe (error "The returned list was empty")
  $ getFirst
  $ foldMap First
  $ sampleN @System 1000000
  $ withClockResetEnable clockGen resetGen enableGen
  $ newsfeed
  $ clu (SNat @4) (SNat @36)
  $ channel
  $ fmap ((op, (a, b)), )
  $ fromList
  $ Keep : Keep : Release : List.repeat Keep
