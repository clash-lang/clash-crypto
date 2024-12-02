{-|
Module      : Test.Clash.Crypto.Hash.SHA
Copyright   : Copyright © 2024 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Hash.SHA'.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedLists #-}

module Test.Clash.Crypto.Hash.SHA where

import Clash.Prelude
import Clash.Sized.Vector (unsafeFromList)

import Data.ByteString (ByteString)
import Data.Constraint
import Data.Constraint.Nat.Extra
import Data.Maybe
import Data.Proxy
import Hedgehog
import Language.Haskell.Unicode (type (≤))
import Test.Tasty
import Test.Tasty.Hedgehog

import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Crypto.Hash.SHA1    as SHA1
import qualified Crypto.Hash.SHA224  as SHA224
import qualified Crypto.Hash.SHA256  as SHA256
import qualified Crypto.Hash.SHA384  as SHA384
import qualified Crypto.Hash.SHA512  as SHA512
import qualified Crypto.Hash.SHA512t as SHA512t

import qualified Data.ByteString as BS
import qualified Data.List as List

import Clash.Crypto.Hash.SHA

import qualified Clash.Crypto.Hash.SHA.Specification as Spec

tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.Hash.SHA"
  [ localOption (HedgehogTestLimit $ Just 4)
      $ testGroup "Specification Sanity Checks (unit tests)"
          [ testProperty ("SHA-" <> algName)
              $ property
              $ forAll (Gen.element inputs)
                  >>= hashPure
          | let inputs = [input1, input2, input3, input4] :: [ByteString]
          , (hashPure, algName) ←
              [ (testHashPure @SHA1,      "1")
              , (testHashPure @SHA224,    "224")
              , (testHashPure @SHA256,    "256")
              , (testHashPure @SHA512,    "512")
              , (testHashPure @SHA512224, "512/224")
              , (testHashPure @SHA512256, "512/246")
              ]
          ]
  , testGroup "Streaming Implementation"
      [ testGroup "Contiguous Input (property based tests)"
          [ testProperty ("SHA-" <> algName)
              $ property
              $ forAll (Gen.bytes $ Range.linear 100 1000)
                  >>= hashStream
          | (hashStream, algName) ←
              [ (testHashCStream @SHA1,      "1")
              , (testHashCStream @SHA224,    "224")
              , (testHashCStream @SHA256,    "256")
              , (testHashCStream @SHA512,    "512")
              , (testHashCStream @SHA512224, "512/224")
              , (testHashCStream @SHA512256, "512/246")
              ]
          ]
      , testGroup "Non-contiguous Input"
          [ localOption (HedgehogTestLimit $ Just 1)
              $ testProperty "SHA-256 HITLT failure (reproducer)"
              $ property
              $ testHashNCStream @SHA256
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
              [ (testHashNCStream @SHA1,      "1")
              , (testHashNCStream @SHA224,    "224")
              , (testHashNCStream @SHA256,    "256")
              , (testHashNCStream @SHA512,    "512")
              , (testHashNCStream @SHA512224, "512/224")
              , (testHashNCStream @SHA512256, "512/246")
              ]
          ]
      ]
  ]

-- | Purely functional hash computation according to the
-- specification.
testHashPure ∷
  ∀ (alg ∷ SHA) m.
  (Monad m, KnownSHA alg, CryptoHash alg) ⇒
  ByteString →
  -- ^ input data
  PropertyT m ()
testHashPure bs
  | SHAFacts alg ← knownSHA @alg
  , Dict ← cancelMultiple @(MessageDigestSize alg) @8
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
    resultDigestAsBv = Spec.hash @alg @(n * 8) inputAsBv

    resultDigestAsVBv8 ∷ Vec (MessageDigestSize alg `Div` 8) (BitVector 8)
    resultDigestAsVBv8 = unconcatBitVector# resultDigestAsBv

    dut = toList $ unpack <$> resultDigestAsVBv8
    ref = BS.unpack $ cryptoHash alg bs

  ref === dut

-- | Tests on a contiguous data input stream.
testHashCStream ∷
  ∀ (alg ∷ SHA) m.
  ( Monad m, KnownSHA alg, CryptoHash alg
  , 8 ≤ BlockSize alg, BlockSize alg `Mod` 8 ~ 0
  ) ⇒
  ByteString →
  -- ^ input data
  PropertyT m ()
testHashCStream
  = testHashNCStream @alg
  . fmap ((, 0) . pack)
  . BS.unpack

-- | Tests on a non-contiguous data input stream.
testHashNCStream ∷
  ∀ (alg ∷ SHA) m.
  ( Monad m, KnownSHA alg, CryptoHash alg
  , 8 ≤ BlockSize alg, BlockSize alg `Mod` 8 ~ 0
  ) ⇒
  [(BitVector 8, Int)] →
  -- ^ input data, where each byte in the first component is followed
  -- by the number of idle cycles stated in the second component
  PropertyT m ()
testHashNCStream xs
  | SHAFacts alg ← knownSHA @alg
  , Dict ← cancelMultiple @(MessageDigestSize alg) @8
  = let
      ncs = List.concatMap
              (\(c, j) → Just (c, Nothing) : List.replicate j Nothing)
              xs

      n = List.length ncs

      sc = max
        (natToNum @(ScheduleCount alg))
        (natToNum @(BlockSize alg) `div` 8)

      requiredSamples =
        sc * (n `div` sc + if n `mod` sc > 0 then 3 else 2) + 4

      inputPlusCtrl ∷ [Maybe (BitVector 8, Maybe (Index 9))]
      inputPlusCtrl
        = [ Nothing, Nothing, Nothing ]
       <> ncs
       <> [ Just (0, Just maxBound) ]
       <> List.replicate requiredSamples Nothing

      inputAsSignal ∷ Signal System (Maybe (BitVector 8, Maybe (Index 9)))
      inputAsSignal = fromList inputPlusCtrl

      output = sampleN (n + requiredSamples) $ sha @alg inputAsSignal

      resultDigestAsVBv8 ∷ Vec (MessageDigestSize alg `Div` 8) (BitVector 8)
      resultDigestAsVBv8
        = unconcatBitVector#
        $ maybe 0 fst
        $ List.uncons
        $ catMaybes output

      ref = BS.unpack $ cryptoHash alg $ BS.pack $ fmap (unpack . fst) xs
      dut = toList $ unpack <$> resultDigestAsVBv8
    in
      ref === dut

class CryptoHash (alg ∷ SHA) where
  cryptoHash ∷ Proxy alg → ByteString → ByteString

instance CryptoHash SHA1      where cryptoHash _ = SHA1.hash
instance CryptoHash SHA224    where cryptoHash _ = SHA224.hash
instance CryptoHash SHA256    where cryptoHash _ = SHA256.hash
instance CryptoHash SHA384    where cryptoHash _ = SHA384.hash
instance CryptoHash SHA512    where cryptoHash _ = SHA512.hash
instance CryptoHash SHA512224 where cryptoHash _ = SHA512t.hash 224
instance CryptoHash SHA512256 where cryptoHash _ = SHA512t.hash 256

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
