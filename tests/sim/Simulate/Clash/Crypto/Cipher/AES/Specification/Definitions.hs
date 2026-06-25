{-|
Module      : Simulate.Clash.Crypto.Cipher.AES.Specification.Definitions
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Cipher.AES.Specification.Definitions'.
-}

module Simulate.Clash.Crypto.Cipher.AES.Specification.Definitions
  ( tastyTests
  ) where

import Clash.Prelude.Safe

import Clash.Hedgehog.Sized.BitVector (genDefinedBitVector)
import Clash.Hedgehog.Sized.Vector (genVec)

import Hedgehog ((===), property, forAll)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Clash.Crypto.Cipher.AES

tastyTests ∷ TestTree
tastyTests = testGroup "Definitions"
  [ testProperty "XOR" $ property $ do
      a ← forAll genDefinedBitVector
      b ← forAll genDefinedBitVector
      a ⊕ b === xor @(BitVector 8) a b
  , testProperty "subBytes" $ property $ do
      a ← forAll $ genVec $ genVec genDefinedBitVector
      a === invSubBytes (subBytes a)
  , testProperty "mixColumns" $ property $ do
      a ← forAll $ genVec $ genVec  genDefinedBitVector
      a === invMixColumns (mixColumns a)
  , testProperty "shiftRows" $ property $ do
      a ← forAll $ genVec $ genVec genDefinedBitVector
      invShiftRows (shiftRows a) === a
  , testProperty "addRoundKey" $ property $ do
      a ← forAll $ genVec $ genVec  genDefinedBitVector
      b ← forAll $ genVec $ genVec  genDefinedBitVector
      a === invAddRoundKey (addRoundKey a b) b
  ]
