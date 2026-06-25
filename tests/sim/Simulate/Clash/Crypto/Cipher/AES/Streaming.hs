{-|
Module      : Simulate.Clash.Crypto.Cipher.AES.Streaming
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Cipher.AES.Streaming'.
-}

module Simulate.Clash.Crypto.Cipher.AES.Streaming
  ( tastyTests
  ) where

import Clash.Prelude.Safe

import Clash.Signal.Channel (Channel, ProviderAction(..), channel, newsfeed)
import Clash.Sized.Vector (unsafeFromList)

import Data.ByteString (ByteString)
import Data.Maybe (fromMaybe)
import Data.Monoid (First(..))
import Hedgehog (PropertyT, (===), forAll, property)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import qualified Data.ByteString as BS (pack, unpack)
import qualified Data.List       as List (repeat)
import qualified Hedgehog.Gen    as Gen (enumBounded, list)
import qualified Hedgehog.Range  as Range (singleton)

import Clash.Crypto.Cipher.AES
import Test.Clash.Crypto.Cipher.AES

tastyTests ∷
  ∀ (alg ∷ AES) → (KnownAES alg, AESKeyExpansion alg, CryptoAES alg) ⇒
  TestTree
tastyTests alg = testGroup "Sanity Checks against crypton"
  [ testProperty "Encryption" $ property
  $ testAESStreaming alg aesECBencryption encryptoECB
  , testProperty "Decryption" $ property
  $ testAESStreaming alg aesECBdecryption decryptoECB
  ]

testAESStreaming ∷
  Monad m ⇒
  ∀ (alg ∷ AES) → (KnownAES alg, AESKeyExpansion alg, CryptoAES alg) ⇒
  ( HiddenClockResetEnable System ⇒
    ∀ (alg1 ∷ AES) → (KnownAES alg1, AESKeyExpansion alg1) ⇒
    Channel System (AESBlock alg1, AESKey alg1) →
    Channel System (AESBlock alg1)
  ) →
  (∀ x → x ~ alg ⇒ ByteString → ByteString → ByteString) →
  PropertyT m ()
testAESStreaming alg action refAction | AESFacts ← knownAES alg = do
  key   ← forAll $ fmap BS.pack
        $ Gen.list (Range.singleton $ natToNum @(Nk alg * AESWordByteCount))
                   Gen.enumBounded
  input ← forAll $ fmap BS.pack
        $ Gen.list (Range.singleton $ natToNum @(Nb alg * AESWordByteCount))
                   Gen.enumBounded

  let inputAsBv8 ∷ [Byte]
      inputAsBv8 = pack <$> BS.unpack input

      inputAsVBv8 ∷ Vec (AESBlockByteCount alg) Byte
      inputAsVBv8 = unsafeFromList inputAsBv8

      inputAsBlock ∷ AESBlock alg
      inputAsBlock = unconcatI inputAsVBv8

      keyAsBv8 ∷ [Byte]
      keyAsBv8 = pack <$> BS.unpack key

      keyAsVBv8 ∷ Vec (Nk alg * AESWordByteCount) Byte
      keyAsVBv8 = unsafeFromList keyAsBv8

      aesKey ∷ AESKey alg
      aesKey = unconcatI keyAsVBv8

      resultDigestAsBv ∷ AESBlock alg
      resultDigestAsBv
        = fromMaybe (error "The returned list was empty")
        $ getFirst
        $ foldMap First
        $ sampleN 10000000
        $ withClockResetEnable clockGen resetGen enableGen
        $ newsfeed
        $ action alg
        $ channel
        $ fmap ((inputAsBlock, aesKey), )
        $ fromList
        $ Keep : Keep : Release : List.repeat Keep

      resultDigestAsVBv8 ∷ Vec (AESBlockByteCount alg) Byte
      resultDigestAsVBv8 = concat resultDigestAsBv

      dut = toList $ unpack <$> resultDigestAsVBv8
      ref = BS.unpack $ refAction alg key input

  ref === dut
