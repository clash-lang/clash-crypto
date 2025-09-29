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
import Clash.Prelude hiding (Mod)
import Clash.Signal.Channel
import Data.Maybe (fromMaybe)
import Data.Monoid (First(..))

import Data.Proxy(Proxy(..))
import Clash.Hedgehog.Sized.BitVector (genDefinedBitVector)
import Clash.Hedgehog.Sized.Vector
import Hedgehog
import Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog

import Clash.Crypto.Cipher.AES
import Clash.Crypto.Cipher.AES.Specification as Spec
import Clash.Crypto.Cipher.AES.Streaming.Algorithm as Stream
import qualified Data.List as List
tastyTests :: TestTree
tastyTests = testGroup "Clash.Crypto.Cipher.AES.Streaming.Algorithm"
  [ localOption (HedgehogTestLimit (Just 10)) $ testGroup "Verification equality of hardware and functional"[
      testProperty "Cipher version AES128" $ cipherProperty @AES128 (Stream.cipher @AES128) Spec.cipher,
      localOption (HedgehogTestLimit (Just 10)) $
      testProperty "Cipher version AES192" $ cipherProperty @AES192 (Stream.cipher @AES192) Spec.cipher,
      localOption (HedgehogTestLimit (Just 10)) $
      testProperty "Cipher version AES256" $ cipherProperty @AES256 (Stream.cipher @AES256) Spec.cipher,
      
      testProperty "InvCipher version AES128" $ cipherProperty @AES128 (Stream.invCipher @AES128) Spec.invCipher,
      localOption (HedgehogTestLimit (Just 10)) $
      testProperty "InvCipher version AES192" $ cipherProperty @AES192 (Stream.invCipher @AES192) Spec.invCipher,
      localOption (HedgehogTestLimit (Just 10)) $
      testProperty "InvCipher version AES256" $ cipherProperty @AES256 (Stream.invCipher @AES256) Spec.invCipher,
      
      testProperty "EqInvCipher version AES128" $ cipherProperty @AES128 (Stream.eqInvCipher @AES128) Spec.eqInvCipher,
      localOption (HedgehogTestLimit (Just 10)) $
      testProperty "EqInvCipher version AES192" $ cipherProperty @AES192 (Stream.eqInvCipher @AES192) Spec.eqInvCipher,
      localOption (HedgehogTestLimit (Just 10)) $
      testProperty "EqInvCipher version AES256" $ cipherProperty @AES256 (Stream.eqInvCipher @AES256) Spec.eqInvCipher
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
    cipherError =
        error "Since the modulo of the field is prime, the inverse always exists."
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
