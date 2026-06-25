{-|
Module      : Simulate.Clash.Crypto.Cipher.AES.Streaming.Algorithm
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Cipher.AES.Streaming.Algorithm'.
-}

module Simulate.Clash.Crypto.Cipher.AES.Streaming.Algorithm
  ( tastyTests
  ) where

import Clash.Prelude.Safe

import Clash.Hedgehog.Sized.BitVector (genDefinedBitVector)
import Clash.Hedgehog.Sized.Vector (genVec)
import Clash.Signal.Channel (Channel, ProviderAction(..), newsfeed, channel)

import Data.Maybe (fromMaybe)
import Data.Monoid (First(..))
import Hedgehog (Property, (===), forAll, property)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import qualified Data.List as List (repeat)

import Clash.Crypto.Cipher.AES
import Clash.Crypto.Cipher.AES.Specification
import Clash.Crypto.Cipher.AES.Streaming.Algorithm

tastyTests ∷
  ∀ (alg ∷ AES) → (KnownAES alg, AESKeyExpansion alg, KnownNat (Nr alg)) ⇒
  TestTree
tastyTests alg = testGroup "Algorithm"
  [ testProperty "Cipher"
  $ cipherProperty alg cipherStream cipher
  , testProperty "InvCipher"
  $ cipherProperty alg invCipherStream invCipher
  , testProperty "EqInvCipher"
  $ cipherProperty alg eqInvCipherStream eqInvCipher
  , testProperty "KeyExpansion"
  $ keyExpansionProperty alg keyExpansionStream keyExpansion
  , testProperty "KeyExpansionIEC"
  $ keyExpansionProperty alg keyExpansionIECStream keyExpansionIEC
  ]

cipherProperty ∷
  ∀ (alg ∷ AES) → KnownAES alg ⇒
  ( HiddenClockResetEnable System ⇒
    ∀ (alg1 ∷ AES) → KnownAES alg1 ⇒
    Channel System (AESBlock alg1, KeySchedule alg1) →
    Channel System (AESBlock alg1)
  ) →
  ( AESFunctions alg ⇒
    ∀ x → x ~ alg ⇒
    AESBlock alg →
    KeySchedule alg →
    AESBlock alg
  ) →
  Property
cipherProperty alg cipherComp0 cipherComp1 | AESFacts ← knownAES alg =
  property $ do
    inputAsInType ← forAll $ genVec @(Nb alg)
                  $ genVec @AESWordByteCount genDefinedBitVector
    wAsInType     ← forAll $ genVec @((Nr alg + 1) * 4)
                  $ genVec @AESWordByteCount genDefinedBitVector
    sim (cipherComp0 alg) (inputAsInType, wAsInType)
      === cipherComp1 alg inputAsInType wAsInType

keyExpansionProperty ∷
  ∀ (alg ∷ AES) → (KnownAES alg, AESKeyExpansion alg, KnownNat (Nr alg)) ⇒
  ( (HiddenClockResetEnable System, AESKeyExpansion alg) ⇒
    ∀ x → (x ~ alg, KnownAES alg) ⇒
    Channel System (AESKey alg) →
    Channel System (KeySchedule alg)
  ) →
  (AESFunctions alg ⇒ ∀ x → x ~ alg ⇒ AESKey alg → KeySchedule alg) →
  Property
keyExpansionProperty alg keyComp0 keyComp1 | AESFacts ← knownAES alg =
  property $ do
    keyAsInType ← forAll $ genVec @(Nk alg)
                $ genVec @AESWordByteCount genDefinedBitVector
    sim (keyComp0 alg) keyAsInType === keyComp1 alg keyAsInType

sim ∷
  (KnownDomain dom, NFDataX b) ⇒
  (HiddenClockResetEnable dom ⇒ Channel dom a → Channel dom b) →
  a → b
sim action input
  = fromMaybe (error "The returned list was empty")
  $ getFirst
  $ foldMap First
  $ sampleN 10000000
  $ withClockResetEnable clockGen resetGen enableGen
  $ newsfeed
  $ action
  $ channel
  $ fmap (input, )
  $ fromList
  $ Keep : Keep : Release : List.repeat Keep
