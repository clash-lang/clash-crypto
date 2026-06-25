{-|
Module      : Simulate.Clash.Crypto.Cipher.AES.Specification.Algorithm
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Cipher.AES.Specification.Algorithm'.
-}

module Simulate.Clash.Crypto.Cipher.AES.Specification.Algorithm
  ( tastyTests
  ) where

import Clash.Prelude.Safe

import Clash.Hedgehog.Sized.BitVector (genDefinedBitVector)
import Clash.Hedgehog.Sized.Vector (genVec)

import Hedgehog ((===), forAll, property)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Clash.Crypto.Cipher.AES
import Clash.Crypto.Cipher.AES.Specification

tastyTests ∷
  ∀ (alg ∷ AES) → (AESFunctions alg, KnownNat (Nk alg)) ⇒
  TestTree
tastyTests alg = testGroup "Algorithm"
  [ testProperty "Cipher/InvCipher" $ property $ do
      input ← forAll $ genVec @(Nb alg)
            $ genVec @AESWordByteCount genDefinedBitVector
      key   ← forAll $ genVec @(Nk alg)
            $ genVec @AESWordByteCount genDefinedBitVector
      input === invCipher alg
                  (cipher alg input (keyExpansion alg key))
                  (keyExpansion alg key)
  , testProperty "Inverse Cipher" $ property $ do
      input ← forAll $ genVec @(Nb alg)
            $ genVec @AESWordByteCount genDefinedBitVector
      key   ← forAll $ genVec @(Nk alg)
            $ genVec @AESWordByteCount genDefinedBitVector
      invCipher alg input (keyExpansion alg key)
        === eqInvCipher alg input (keyExpansionIEC alg key)
  ]
