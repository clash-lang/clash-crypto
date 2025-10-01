{-|
Module      : Test.Clash.Crypto.Cipher.AES.Streaming
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Cipher.AES.Streaming'.
-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedLists #-} -- Used to inturper a list as Byte String
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}

module Test.Clash.Crypto.Cipher.AES.Streaming (tastyTests) where

import Clash.Crypto.Cipher.AES
import Clash.Prelude

import Clash.Sized.Vector (unsafeFromList)

-- https://hackage.haskell.org/package/clash-prelude-hedgehog
import Hedgehog
import qualified Hedgehog.Gen as Gen

import Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog


-- Test AES128
import Test.Clash.Crypto.Cipher.AES.GoldenReference as Reference 
import Data.ByteString (ByteString) 
import qualified Data.ByteString as BS

import qualified Clash.Crypto.Cipher.AES.Specification as Spec
import qualified Test.Clash.Crypto.Cipher.AES.Streaming.Algorithm as Alg
import qualified Data.List as List
import Clash.Signal.Channel
import Data.Maybe (fromMaybe)
import Data.Monoid (First(..))
tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.Cipher.AES.Streaming"
  [Alg.tastyTests
  , tastyTestsAESStream]
tastyTestsAESStream ∷ TestTree
tastyTestsAESStream = testGroup "Clash.Crypto.Cipher.AES.Streaming"
  [ localOption (HedgehogTestLimit (Just 10)) $
      testGroup "Streaming Sanity Checks against haskell crypton AES128 \nEncryption ECB mode"
        [ 
          testProperty "AES128" $
            property $ do
              key <- forAll $ genKeyFor @(Spec.AES128 ∷ Spec.AES)
              input <- forAll $ genInputBlock @(Spec.AES128 ∷ Spec.AES)
              testAESPureDecryption @Spec.AES128 key input,
        testProperty "AES-128, specific key" $
            property $ do
              testAESPureEncryption @Spec.AES128 in1AES128 key1AES128 
        ]
        ,
        testGroup "Streaming Sanity Checks against haskell crypton AES192 \nEncryption ECB mode" $
        [ testProperty ("AES-" <> algName) $
            property $ do
              key <- forAll $ genKeyFor @(Spec.AES192 ∷ Spec.AES)
              input <- forAll $ genInputBlock @(Spec.AES192 ∷ Spec.AES)
              aesPure key input
        | (aesPure, algName) <-
            [ (testAESPureEncryption @Spec.AES192, "192")
            ]
        ]
        ,
        testGroup "Streaming Sanity Checks against haskell crypton AES256 \nEncryption ECB mode" $
        [ testProperty ("AES-" <> algName) $
            property $ do
              key <- forAll $ genKeyFor @(Spec.AES256 ∷ Spec.AES)
              input <- forAll $ genInputBlock @(Spec.AES256 ∷ Spec.AES)
              aesPure key input
        | (aesPure, algName) <-
            [ (testAESPureEncryption @Spec.AES256, "256")
            ]
        ]
        ,
        testGroup "Streaming Sanity Checks against haskell crypton AES128 \nDecryption ECB mode"
        [ 
          testProperty "AES128" $
            property $ do
              key <- forAll $ genKeyFor @(Spec.AES128 ∷ Spec.AES)
              input <- forAll $ genInputBlock @(Spec.AES128 ∷ Spec.AES)
              testAESPureDecryption @Spec.AES128 key input,
        testProperty "AES-128, specific key" $
            property $ do
              testAESPureDecryption @Spec.AES128 in1AES128 key1AES128 
        ]
        ,
        testGroup "Streaming Sanity Checks against haskell crypton AES192 \nDecryption ECB mode" $
        [ testProperty ("AES-" <> algName) $
            property $ do
              key <- forAll $ genKeyFor @(Spec.AES192 ∷ Spec.AES)
              input <- forAll $ genInputBlock @(Spec.AES192 ∷ Spec.AES)
              aesPure key input
        | (aesPure, algName) <-
            [ (testAESPureDecryption @Spec.AES192, "192")
            ]
        ]
        ,
        testGroup "Streaming Sanity Checks against haskell crypton AES256 \nDecryption ECB mode" $
        [ testProperty ("AES-" <> algName) $
            property $ do
              key <- forAll $ genKeyFor @(Spec.AES256 ∷ Spec.AES)
              input <- forAll $ genInputBlock @(Spec.AES256 ∷ Spec.AES)
              aesPure key input
        | (aesPure, algName) <-
            [ (testAESPureDecryption @Spec.AES256, "256")
            ]
        ]
  ]
genInputBlock ∷ ∀ (alg ∷ Spec.AES). Spec.KnownAES alg => Gen ByteString
genInputBlock 
    | AESFacts _ ← knownAES @alg =
    BS.pack <$> Gen.list (Range.singleton (snatToNum (SNat @(Spec.Nb alg * Spec.WordSize alg)))) Gen.enumBounded
genKeyFor :: ∀ (alg ∷ Spec.AES). Spec.KnownAES alg => Gen ByteString
genKeyFor   
  | AESFacts _ ← knownAES @alg = do
  BS.pack <$> Gen.list (Range.singleton (natToNum @( Spec.WordSize alg  * Spec.Nk alg ))) Gen.enumBounded





testAESPureEncryption ∷ ∀ (alg ∷ Spec.AES) m.
  (Monad m, KnownAES alg, KnownAESStream alg, AESKeyExpansion alg, CryptoAES alg) ⇒
  ByteString →
  -- ^ input data
    ByteString →
  -- ^ key data
  PropertyT m ()
testAESPureEncryption key input
  | AESFacts alg ← knownAES @alg
  -- , Rewrite ← using @(CancelMultiple (MessageDigestSize alg) 8)
  = do

  -- Just (SomeNat (_ ∷ Proxy n)) ←
  --   return $ someNatVal $ toInteger $ BS.length input

  let
    inputAsBv8 ∷ [BitVector 8]
    inputAsBv8 = pack <$> BS.unpack input

    inputAsVBv8 ∷ Vec (Nb alg * WordSize alg)  (BitVector 8)
    inputAsVBv8 = unsafeFromList @(Nb alg * WordSize alg) inputAsBv8

    inputAsInType ∷ InType alg
    inputAsInType = unconcatI inputAsVBv8

    keyAsBv8 ∷ [BitVector 8]
    keyAsBv8 = pack <$> BS.unpack key

    keyAsVBv8 ∷ Vec (Nk alg * WordSize alg)  (BitVector 8)
    keyAsVBv8 = unsafeFromList @(Nk alg * WordSize alg) keyAsBv8
    keyAsInType ∷ KeyType alg
    keyAsInType = unconcatI keyAsVBv8

    resultDigestAsBv ∷ OutType alg
    resultDigestAsBv = compute (inputAsInType, keyAsInType)

    resultDigestAsVBv8 ∷ Vec (Nb alg * WordSize alg) (BitVector 8)
    resultDigestAsVBv8 = concat resultDigestAsBv

    dut = toList $ unpack <$> resultDigestAsVBv8
    ref = BS.unpack $ Reference.encryptoECB alg key input
  ref === dut
    where
      compute input
        = fromMaybe (error "The returned list was empty")
            $ getFirst
            $ foldMap First
            $ sampleN @System 10000000
            $ withClockResetEnable @System clockGen resetGen enableGen
            $ newsfeed
            $ aesECBencryption @alg
            $ channel
            $ fmap (input, )
            $ fromList
            $ Keep : Keep : Release : List.repeat Keep

testAESPureDecryption ∷ ∀ (alg ∷ Spec.AES) m.
  (Monad m, KnownAES alg, KnownAESStream alg, AESKeyExpansion alg, CryptoAES alg) ⇒
  ByteString →
  -- ^ input data
    ByteString →
  -- ^ key data
  PropertyT m ()
testAESPureDecryption key input
  | AESFacts alg ← knownAES @alg
  -- , Rewrite ← using @(CancelMultiple (MessageDigestSize alg) 8)
  = do

  -- Just (SomeNat (_ ∷ Proxy n)) ←
  --   return $ someNatVal $ toInteger $ BS.length input

  let
    inputAsBv8 ∷ [BitVector 8]
    inputAsBv8 = pack <$> BS.unpack input

    inputAsVBv8 ∷ Vec (Nb alg * WordSize alg)  (BitVector 8)
    inputAsVBv8 = unsafeFromList @(Nb alg * WordSize alg) inputAsBv8

    inputAsInType ∷ InType alg
    inputAsInType = unconcatI inputAsVBv8

    keyAsBv8 ∷ [BitVector 8]
    keyAsBv8 = pack <$> BS.unpack key

    keyAsVBv8 ∷ Vec (Nk alg * WordSize alg)  (BitVector 8)
    keyAsVBv8 = unsafeFromList @(Nk alg * WordSize alg) keyAsBv8
    keyAsInType ∷ KeyType alg
    keyAsInType = unconcatI keyAsVBv8

    resultDigestAsBv ∷ OutType alg
    resultDigestAsBv = compute (inputAsInType, keyAsInType)

    resultDigestAsVBv8 ∷ Vec (Nb alg * WordSize alg) (BitVector 8)
    resultDigestAsVBv8 = concat resultDigestAsBv

    dut = toList $ unpack <$> resultDigestAsVBv8
    ref = BS.unpack $ Reference.decryptoECB alg key input
  ref === dut
    where
      compute input
        = fromMaybe (error "The returned list was empty")
            $ getFirst
            $ foldMap First
            $ sampleN @System 10000000
            $ withClockResetEnable @System clockGen resetGen enableGen
            $ newsfeed
            $ aesECBdecryption @alg
            $ channel
            $ fmap (input, )
            $ fromList
            $ Keep : Keep : Release : List.repeat Keep

-- | Some example input for unit testing.
in1AES128 ∷ ByteString
in1AES128 = [0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d, 0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34]
key1AES128 ∷ ByteString
key1AES128 = [ 0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c ]


