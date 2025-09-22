{-|
Module      :  Test.Clash.Crypto.Cipher.AES.Specifications.Defintions
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Cipher.AES'.
-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}

module Test.Clash.Crypto.Cipher.AES.Specifications.Definitions (tastyTests) where


import Clash.Crypto.Cipher.AES
import Clash.Prelude
import Clash.Sized.Vector (unsafeFromList)
-- import Data.Maybe (catMaybes, listToMaybe, fromMaybe)

-- https://hackage.haskell.org/package/clash-prelude-hedgehog
import Hedgehog
-- import Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog
-- import qualified Data.List as List
-- import qualified Hedgehog.Range as Range
import Data.Proxy (Proxy(..))
-- Generate BitVecor and Vector
import Clash.Hedgehog.Sized.BitVector (genDefinedBitVector)
import Clash.Hedgehog.Sized.Vector
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.Cipher.AES.Definitions"
  [localOption (HedgehogTestLimit (Just 10)) $ -- Purpose is mainly to get familiar with testing.
      testProperty "Functional equality of XOR" $ property $ do
        a ← forAll $ genDefinedBitVector
        b ← forAll $ genDefinedBitVector
        testOplus a b,
   localOption (HedgehogTestLimit (Just 10)) $
      testProperty "Functional with subBytes" $ property $ do
        a ← forAll $ genVec (genVec  genDefinedBitVector)
        testsubBytes a,
   localOption (HedgehogTestLimit (Just 10)) $
      testProperty "Functional with subBytes" $ property $ do
        a ← forAll $ genVec (genVec  genDefinedBitVector)
        testMixColumns a,
   localOption (HedgehogTestLimit (Just 10)) $
      testProperty "Functional with shiftRows" $ property $ do
        a ← forAll $ genVec (genVec  genDefinedBitVector) 
        testShiftRows a,
  localOption (HedgehogTestLimit (Just 10)) $
      testProperty "Generic functional with addRoundKey fully" $ property $ do
        a ← forAll $ genVec (genVec  genDefinedBitVector) 
        b ← forAll $ genVec (genVec  genDefinedBitVector) 
        testAddRoundKey a b
  ]
type TestLen = 8
testOplus ∷ (Monad m) => BitVector TestLen -> BitVector TestLen -> PropertyT m ()
testOplus a b = a ⊕ b === xor a b 

-- test matrix:
testState ∷ StateType alg
testState = (0x00 :> 0x10 :> 0x20 :> 0x30 :> Nil) :> (0x01 :> 0x11 :> 0x21 :> 0x31 :> Nil) :> (0x02 :> 0x12 :> 0x22 :> 0x32 :> Nil) :> (0x03 :> 0x13 :> 0x23 :> 0x33 :> Nil) :>Nil

-- ShiftRows
testResultShiftRows ∷ StateType alg
testResultShiftRows = (0x00:>0x11:>0x22:>0x33:>Nil):>(0x01:>0x12:>0x23:>0x30:>Nil):>(0x02:>0x13:>0x20:>0x31:>Nil):>(0x03:>0x10:>0x21:>0x32:>Nil):>Nil
testResultInvShiftRows ∷ StateType alg
testResultInvShiftRows = (0x00:>0x13:>0x22:>0x31:>Nil):>(0x01:>0x10:>0x23:>0x32:>Nil):>(0x02:>0x11:>0x20:>0x33:>Nil):>(0x03:>0x12:>0x21:>0x30:>Nil):>Nil
testShiftRows ∷ (Monad m) ⇒ StateType alg -> PropertyT m ()
testShiftRows state = do
  invShiftRows (shiftRows state) === state
  shiftRows testState ===  testResultShiftRows 
  invShiftRows testState ===  testResultInvShiftRows 

-- SubBytes
testStateSubBytes ∷ StateType alg
testStateSubBytes = (0x53:>0x53:>0x53:>0x53:>Nil):>(0x00:>0x00:>0x00:>0x00:>Nil):>(0x53:>0x53:>0x53:>0x53:>Nil):>(0x53:>0x53:>0x53:>0x353:>Nil):>Nil
testResultStateSubBytes ∷ StateType alg
testResultStateSubBytes = (0xed:>0xed:>0xed:>0xed:>Nil):>(0x63:>0x63:>0x63:>0x63:>Nil):>(0xed:>0xed:>0xed:>0xed:>Nil):>(0xed:>0xed:>0xed:>0xed:>Nil):>Nil
testsubBytes ∷ (Monad m) ⇒ StateType alg -> PropertyT m ()
testsubBytes state = do
  state === invSubBytes (subBytes state)
  testResultStateSubBytes === subBytes testStateSubBytes
  invSubBytes testResultStateSubBytes === testStateSubBytes


-- MixColumns
testMixColumns ∷ (Monad m) ⇒ StateType alg -> PropertyT m ()
testMixColumns state = state === invMixColumns (mixColumns state)
-- AddRoundKey
testAddRoundKey ∷ (Monad m) ⇒ StateType alg → RoundWType alg → PropertyT m ()
testAddRoundKey state ws = state === invAddRoundKey (addRoundKey state ws) ws