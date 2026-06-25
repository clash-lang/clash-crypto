{-|
Module      : Simulate.Clash.Crypto.Cipher.AES.Specification
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Cipher.AES.Specification'.
-}

module Simulate.Clash.Crypto.Cipher.AES.Specification
  ( tastyTests
  ) where

import Clash.Prelude.Safe

import Clash.Sized.Vector (unsafeFromList)

import Hedgehog ((===), forAll, property)
import Test.Tasty (TestTree)
import Test.Tasty.Hedgehog (testProperty)

import qualified Data.ByteString as BS (pack, unpack)
import qualified Hedgehog.Gen    as Gen (enumBounded, list)
import qualified Hedgehog.Range  as Range (singleton)

import Clash.Crypto.Cipher.AES
import Clash.Crypto.Cipher.AES.Specification
import Test.Clash.Crypto.Cipher.AES

tastyTests ∷
  ∀ (alg ∷ AES) → (KnownAES alg, CryptoAES alg) ⇒
  TestTree
tastyTests alg | AESFacts ← knownAES alg =
  testProperty "Sanity Checks against crypton" $ property $ do
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
        resultDigestAsBv = aesFunctional alg inputAsBlock aesKey

        resultDigestAsVBv8 ∷ Vec (AESBlockByteCount alg) Byte
        resultDigestAsVBv8 = concat resultDigestAsBv

        dut = toList $ unpack <$> resultDigestAsVBv8
        ref = BS.unpack $ encryptoECB alg key input

    ref === dut
