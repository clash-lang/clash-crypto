{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-|
Module      : Test.Clash.Crypto.Cipher.AES.Streaming.Algorithm 
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Cipher.AES.Streaming.Algorithm'.
-}

module Test.Clash.Crypto.Cipher.AES.Streaming.Algorithm (tastyTests) where
import Clash.Prelude 
import Clash.Signal.Channel
import Data.Maybe (fromMaybe)
import Data.Monoid (First(..))

import Data.Proxy(Proxy(..))
import Clash.Hedgehog.Sized.BitVector (genDefinedBitVector)
import Clash.Hedgehog.Sized.Vector
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog

import Clash.Crypto.Cipher.AES
import Clash.Crypto.Cipher.AES.Specification as Spec
import Clash.Crypto.Cipher.AES.Streaming.Algorithm as Stream
import qualified Data.List as List
tastyTests :: TestTree
tastyTests = testGroup "Clash.Crypto.Cipher.AES.Streaming.Algorithm"
  [ localOption (HedgehogTestLimit (Just 10)) $ testGroup "Verification equality of hardware and functional"
  [
      testProperty "Cipher version AES128" $ cipherProperty @AES128 (Stream.cipherStream @AES128) Spec.cipher,
      testProperty "Cipher version AES192" $ cipherProperty @AES192 (Stream.cipherStream @AES192) Spec.cipher,
      testProperty "Cipher version AES256" $ cipherProperty @AES256 (Stream.cipherStream @AES256) Spec.cipher,
      
      testProperty "InvCipher version AES128" $ cipherProperty @AES128 (Stream.invCipherStream @AES128) Spec.invCipher,
      testProperty "InvCipher version AES192" $ cipherProperty @AES192 (Stream.invCipherStream @AES192) Spec.invCipher,
      testProperty "InvCipher version AES256" $ cipherProperty @AES256 (Stream.invCipherStream @AES256) Spec.invCipher,
      
      testProperty "EqInvCipher version AES128" $ cipherProperty @AES128 (Stream.eqInvCipherStream @AES128) Spec.eqInvCipher,
      testProperty "EqInvCipher version AES192" $ cipherProperty @AES192 (Stream.eqInvCipherStream @AES192) Spec.eqInvCipher,
      testProperty "EqInvCipher version AES256" $ cipherProperty @AES256 (Stream.eqInvCipherStream @AES256) Spec.eqInvCipher,

      testProperty "KeyExpansion version AES128" $ keyExpansionProperty @AES128 (Stream.keyExpansionStream @AES128) Spec.keyExpansion,
      testProperty "KeyExpansion version AES192" $ keyExpansionProperty @AES192 (Stream.keyExpansionStream @AES192) Spec.keyExpansion,
      testProperty "KeyExpansion version AES256" $ keyExpansionProperty @AES256 (Stream.keyExpansionStream @AES256) Spec.keyExpansion,

      testProperty "KeyExpansionIEC version AES128" $ keyExpansionProperty @AES128 (Stream.keyExpansionIECStream @AES128) Spec.keyExpansionIEC,
      testProperty "KeyExpansionIEC version AES192" $ keyExpansionProperty @AES192 (Stream.keyExpansionIECStream @AES192) Spec.keyExpansionIEC,
      testProperty "KeyExpansionIEC version AES256" $ keyExpansionProperty @AES256 (Stream.keyExpansionIECStream @AES256) Spec.keyExpansionIEC
  ]
      ]

type CipherComponent alg dom =
 HiddenClockResetEnable dom =>
 Channel dom (InType alg, WType alg) ->
 Channel dom (OutType alg)
type CipherRefComponent alg =
  Proxy alg -> InType alg -> WType alg -> OutType alg
cipherProperty ∷ ∀ (alg ∷ AES). (KnownAES alg) ⇒ KnownDomain System ⇒  CipherComponent alg System → CipherRefComponent alg → Property
cipherProperty cipherComp cipherComp1
  | AESFacts alg ← knownAES @alg
  = property $ do
    inputAsInType ← forAll $ genVec @(Nb alg) (genVec @(WordSize alg) genDefinedBitVector) 
    wAsInType     ← forAll $ genVec @((Nr alg + 1) * 4) (genVec @(WordSize alg) genDefinedBitVector) 
    let f' = compute (inputAsInType, wAsInType)
    f' === cipherComp1 alg inputAsInType wAsInType
    where
    compute input
        = fromMaybe (error "The returned list was empty")
            $ getFirst
            $ foldMap First
            $ sampleN @System 10000000
            $ withClockResetEnable @System clockGen resetGen enableGen
            $ newsfeed
            $ cipherComp
            $ channel
            $ fmap (input, )
            $ fromList
            $ Keep : Keep : Release : List.repeat Keep

type KeyExpansionComponent alg dom =
 HiddenClockResetEnable dom ⇒ 
 Channel dom (KeyType alg) → 
 Channel dom (WType alg)
type KeyExpansionRefComponent alg =
  Proxy alg -> KeyType alg → WType alg
keyExpansionProperty ∷ ∀ (alg ∷ AES). (KnownAES alg,KnownNat (Nr alg)) ⇒ KnownDomain System ⇒  KeyExpansionComponent alg System → KeyExpansionRefComponent alg → Property
keyExpansionProperty keyComp keyComp1
  | AESFacts alg ← knownAES @alg
  = property $ do
    keyAsInType   ← forAll $ genVec @(Nk alg) (genVec @(WordSize alg) genDefinedBitVector) 
    let f' = compute keyAsInType
    f' === keyComp1 alg keyAsInType
    where
    compute input
        = fromMaybe (error "The returned list was empty")
            $ getFirst
            $ foldMap First
            $ sampleN @System 10000000
            $ withClockResetEnable @System clockGen resetGen enableGen
            $ newsfeed
            $ keyComp
            $ channel
            $ fmap (input, )
            $ fromList
            $ Keep : Keep : Release : List.repeat Keep

