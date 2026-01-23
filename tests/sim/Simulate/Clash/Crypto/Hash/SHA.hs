{-|
Module      : Simulate.Clash.Crypto.Hash.SHA
Copyright   : Copyright © 2024-2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Simulation tests for 'Clash.Crypto.Hash.SHA'.
-}

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedLists #-}

{-# OPTIONS_GHC -Wno-deprecations #-}

module Simulate.Clash.Crypto.Hash.SHA (tastyTests) where

import Clash.Prelude.Safe
import Clash.Signal.Channel
import Clash.Signal.DataStream
import Clash.Sized.Vector (unsafeFromList)

import Data.ByteString (ByteString)
import Data.Constraint.Nat.Extra
import Data.Kind (Type)
import Data.Maybe
import Data.Proxy
import GHC.TypeNats.Proof (Rewrite(..), using)
import Hedgehog
import Language.Haskell.Unicode (type (≤))
import Test.Tasty
import Test.Tasty.Hedgehog

import Test.Clash.Crypto.Hash.SHA

import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Crypto.Hash as Hash
import qualified Data.ByteString as BS
import qualified Data.List as List

import Clash.Crypto.Hash.SHA

import qualified Clash.Crypto.Hash.SHA.Specification as Spec
import Data.Word (Word8)
import Text.Printf (printf)

tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.Hash.SHA"
  [ localOption (HedgehogTestLimit $ Just 4)
      $ testGroup "Sanity Checks (unit tests)"
          [ testProperty ("SHA-" <> algName)
              $ property
              $ forAll (Gen.element inputs)
                  >>= hashPure
          | let inputs = [input1, input2, input3, input4] ∷ [ByteString]
          , (hashPure, algName) ←
              [ (testHashPure SHA1,      "1")
              , (testHashPure SHA224,    "224")
              , (testHashPure SHA256,    "256")
              , (testHashPure SHA512,    "512")
              , (testHashPure SHA512224, "512/224")
              , (testHashPure SHA512256, "512/246")
              ]
          ]
  , testGroup "Streaming"
      [ testGroup "Contiguous Input"
          [ testProperty ("SHA-" <> algName)
              $ property
              $ do xs ← forAll (Gen.bytes $ Range.linear 100 1000)
                   hashStream xs
          | (hashStream, algName) ←
              [ (testHashCStream SHA1,      "1")
              , (testHashCStream SHA224,    "224")
              , (testHashCStream SHA256,    "256")
              , (testHashCStream SHA512,    "512")
              , (testHashCStream SHA512224, "512/224")
              , (testHashCStream SHA512256, "512/246")
              ]
          ]
      , testGroup "Non-contiguous Input"
          [ localOption (HedgehogTestLimit $ Just 1)
              $ testProperty "SHA-256 HITLT failure (reproducer)"
              $ property
              $ testHashNCStream SHA256
              $ List.zip
                  (List.replicate 64 0)
                  (List.replicate 62 0 <> [64, 0])
          ]
      , testGroup "Property Based Tests"
          [ testProperty ("SHA-" <> algName)
              $ property
              $ do bs ← forAll
                     $ Gen.bytes
                     $ Range.linear 80 100
                   xs ← forAll
                     $ Gen.list (Range.singleton $ BS.length bs)
                     $ Gen.integral @_ @Int
                     $ Range.linear 50 100
                   hashStream $ List.zip (pack <$> BS.unpack bs) xs
          | (hashStream, algName) ←
              [ (testHashNCStream SHA1,      "1")
              , (testHashNCStream SHA224,    "224")
              , (testHashNCStream SHA256,    "256")
              , (testHashNCStream SHA512,    "512")
              , (testHashNCStream SHA512224, "512/224")
              , (testHashNCStream SHA512256, "512/246")
              ]
          ]
      ]
  ]

-- | Purely functional hash computation according to the
-- specification.
testHashPure ∷
  ∀ (m ∷ Type → Type). Monad m ⇒
  ∀ (alg ∷ SHA) →
  (KnownSHA alg, CryptoHash alg, Hash.HashAlgorithm (CryptoToHash alg)) ⇒
  ByteString →
  -- ^ input data
  PropertyT m ()
testHashPure alg bs
  | SHAFacts ← knownSHA alg
  , Rewrite ← using @(CancelMultiple (MessageDigestSize alg) 8)
  = do

  Just (SomeNat (_ ∷ Proxy n)) ←
    return $ someNatVal $ toInteger $ BS.length bs

  let
    inputAsBv8 ∷ [BitVector 8]
    inputAsBv8 = pack <$> BS.unpack bs

    inputAsVBv8 ∷ Vec n (BitVector 8)
    inputAsVBv8 = unsafeFromList @n inputAsBv8

    inputAsBv ∷ Message (n * 8)
    inputAsBv = concatBitVector# inputAsVBv8

    resultDigestAsBv ∷ BitVector (MessageDigestSize alg)
    resultDigestAsBv = Spec.hash alg inputAsBv

    resultDigestAsVBv8 ∷ Vec (MessageDigestSize alg `Div` 8) (BitVector 8)
    resultDigestAsVBv8 = unconcatBitVector# resultDigestAsBv

    pr = List.concatMap (printf "%02x " ∷ Word8 → String) . BS.unpack

    dut = BS.pack $ toList $ unpack <$> resultDigestAsVBv8
    ref = cryptoHash alg bs

  pr ref === pr dut

-- | Tests on a contiguous data input stream.
testHashCStream ∷
  ∀ (m ∷ Type → Type). Monad m ⇒
  ∀ (alg ∷ SHA) →
  (KnownSHA alg, CryptoHash alg, Hash.HashAlgorithm (CryptoToHash alg)) ⇒
  (8 ≤ BlockSize alg, BlockSize alg `Mod` 8 ~ 0) ⇒
  ByteString →
  -- ^ input data
  PropertyT m ()
testHashCStream alg
  = testHashNCStream alg
  . fmap ((, 0) . pack)
  . BS.unpack

-- | Tests on a non-contiguous data input stream.
testHashNCStream ∷
  ∀ (m ∷ Type → Type). Monad m ⇒
  ∀ (alg ∷ SHA) → (KnownSHA alg, CryptoHash alg,
                   Hash.HashAlgorithm (CryptoToHash alg)) ⇒
  (8 ≤ BlockSize alg, BlockSize alg `Mod` 8 ~ 0) ⇒
  [(BitVector 8, Int)] →
  -- ^ input data, where each byte in the first component is followed
  -- by the number of idle cycles stated in the second component. The
  -- list must be non-empty.
  PropertyT m ()
testHashNCStream alg xs
  | SHAFacts ← knownSHA alg
  , Rewrite ← using @(CancelMultiple (MessageDigestSize alg) 8)
  = let
      upd f (x, j) = f x : List.replicate j NoData

      ncMessage = case List.unsnoc xs of
        Nothing           → []
        Just (ys, (y, _)) → case List.uncons ys of
            Nothing      → [End 0 y]
            Just (z, zs) → upd (Start ()) z
                        <> List.concatMap (upd Middle) zs
                        <> [End 0 y]

      n = List.length ncMessage

      sc = max
        (natToNum @(ScheduleCount alg))
        (natToNum @(BlockSize alg) `div` 8)

      requiredSamples =
        sc * (n `div` sc + if n `mod` sc > 0 then 3 else 2) + 4

      input ∷ DataStream System () (Index 8) (BitVector 8)
      input = fromList i
       where
        i = [Idle, Idle, Idle] <> ncMessage
         <> List.replicate requiredSamples Idle <> i

      output ∷ [Maybe (Digest alg)]
      output = sampleN (2 * (n + requiredSamples)) $ newsfeed $ sha alg input

      resultDigestAsVBv8 ∷ Vec (MessageDigestSize alg `Div` 8) (BitVector 8)
      resultDigestAsVBv8 = case List.take 2 $ catMaybes output of
        []                    → error "No response received."
        [_]                   → error "Missing second response."
        a : b : _ | a /= b    → error "Repeated hashs differ."
                  | otherwise → unconcatBitVector# a

      pr = List.concatMap (printf "%02x " ∷ Word8 → String) . BS.unpack

      ref = cryptoHash alg $ BS.pack $ fmap (unpack . fst) xs
      dut = BS.pack $ toList $ unpack <$> resultDigestAsVBv8
    in
      pr ref === pr dut


-- | Some example input for unit testing.
input1 ∷ ByteString
input1 =
  [ 255, 23, 42, 38, 29, 48, 244, 65, 2, 99 ]

-- | Some example input for unit testing.
input2 ∷ ByteString
input2 =
  [ 255, 23, 42, 38, 29, 48, 244, 65, 2, 99, 41, 31, 231, 199, 25, 32
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  , 255, 23, 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 231
  ]

-- | Some example input for unit testing.
input3 ∷ ByteString
input3 =
  [ 255, 23, 42, 38, 29, 48, 244, 65, 2, 99, 41, 31, 231, 199, 25, 32
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  , 255, 23, 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 231
  , 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 255, 23, 231
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  ]

-- | Some example input for unit testing.
input4 ∷ ByteString
input4 =
  [ 255, 23, 42, 38, 29, 48, 244, 65, 2, 99, 41, 31, 231, 199, 25, 32
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  , 255, 23, 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 231
  , 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 255, 23, 231
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  , 255, 23, 42, 38, 29, 48, 244, 65, 2, 99, 41, 31, 231, 199, 25, 32
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  , 255, 23, 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 231
  , 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 255, 23, 231
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  ]
