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

module Test.Clash.Crypto.Hash.SHA where

import Clash.Prelude
import Clash.Sized.Vector (unsafeFromList)

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

import qualified Crypto.Hash.SHA1 as SHA1
import qualified Crypto.Hash.SHA224 as SHA224
import qualified Crypto.Hash.SHA256 as SHA256
import qualified Crypto.Hash.SHA384 as SHA384
import qualified Crypto.Hash.SHA512 as SHA512
import qualified Crypto.Hash.SHA512t as SHA512t
import qualified Data.ByteString as BS
import qualified Data.List as List

import Clash.Crypto.Hash.SHA

import qualified Clash.Crypto.Hash.SHA.Specification as Spec

tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.Hash.SHA"
  [ localOption (HedgehogTestLimit (Just 4))
  $ testGroup "Specification: sanity checks / unit tests"
      [ testProperty ("SHA-" <> algName)
          $ property
          $ forAll (Gen.element inputs)
              >>= hashPure
      | (hashPure, algName) ←
          [ (testHashPure @SHA1,      "1")
          , (testHashPure @SHA224,    "224")
          , (testHashPure @SHA256,    "256")
          , (testHashPure @SHA512,    "512")
          , (testHashPure @SHA512224, "512/224")
          , (testHashPure @SHA512256, "512/246")
          ]
      , let inputs = [input1, input2, input3, input4]
      ]
  , testGroup "Streaming: property based tests"
      [ testProperty ("SHA-" <> algName)
          $ property
          $ forAll (Gen.bytes $ Range.linear 0 1000)
              >>= hashStream
      | (hashStream, algName) ←
          [ (testHashStream @SHA1,      "1")
          , (testHashStream @SHA224,    "224")
          , (testHashStream @SHA256,    "256")
          , (testHashStream @SHA512,    "512")
          , (testHashStream @SHA512224, "512/224")
          , (testHashStream @SHA512256, "512/246")
          ]
      ]
  ]

testHashPure ∷
  ∀ (alg ∷ SHA) m.
  (Monad m, KnownSHA alg, CryptoHash alg) ⇒
  BS.ByteString →
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

testHashStream ∷
  ∀ (alg ∷ SHA) m.
  ( Monad m, KnownSHA alg, CryptoHash alg
  , 8 ≤ BlockSize alg, BlockSize alg `Mod` 8 ~ 0
  ) ⇒
  BS.ByteString →
  PropertyT m ()
testHashStream bs
  | SHAFacts alg ← knownSHA @alg
  , Dict ← cancelMultiple @(MessageDigestSize alg) @8
  = do

  let
    inputAsBv8 ∷ [BitVector 8]
    inputAsBv8 = pack <$> BS.unpack bs

    n = List.length inputAsBv8

    sc = max
      (natToNum @(ScheduleCount alg))
      (natToNum @(BlockSize alg) `div` 8)

    requiredSamples =
      sc * (n `div` sc + if n `mod` sc > 0 then 3 else 2) + 4

    inputPlusCtrl ∷ [Maybe (BitVector 8, Maybe (Index 9))]
    inputPlusCtrl
      = [ Nothing, Nothing, Nothing ]
     <> ( Just . (, Nothing) <$> inputAsBv8 )
     <> [ Just (0, Just maxBound) ]
     <> List.replicate requiredSamples Nothing

    inputAsSignal ∷ Signal System (Maybe (BitVector 8, Maybe (Index 9)))
    inputAsSignal = fromList inputPlusCtrl

    output = sampleN requiredSamples $ sha @alg inputAsSignal

    resultDigestAsVBv8 ∷ Vec (MessageDigestSize alg `Div` 8) (BitVector 8)
    resultDigestAsVBv8
      = unconcatBitVector#
      $ maybe 0 fst
      $ List.uncons
      $ catMaybes output

    dut = toList $ unpack <$> resultDigestAsVBv8
    ref = BS.unpack $ cryptoHash alg bs

  ref === dut

class CryptoHash (alg ∷ SHA) where
  cryptoHash ∷ Proxy alg → BS.ByteString → BS.ByteString

instance CryptoHash SHA1      where cryptoHash _ = SHA1.hash
instance CryptoHash SHA224    where cryptoHash _ = SHA224.hash
instance CryptoHash SHA256    where cryptoHash _ = SHA256.hash
instance CryptoHash SHA384    where cryptoHash _ = SHA384.hash
instance CryptoHash SHA512    where cryptoHash _ = SHA512.hash
instance CryptoHash SHA512224 where cryptoHash _ = SHA512t.hash 224
instance CryptoHash SHA512256 where cryptoHash _ = SHA512t.hash 256

input1 ∷ BS.ByteString
input1 = BS.pack [ 255, 23, 42, 38, 29, 48, 244, 65, 2, 99 ]

input2 ∷ BS.ByteString
input2 = BS.pack
  [ 255, 23, 42, 38, 29, 48, 244, 65, 2, 99, 41, 31, 231, 199, 25, 32
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  , 255, 23, 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 231
  ]

input3 ∷ BS.ByteString
input3 = BS.pack
  [ 255, 23, 42, 38, 29, 48, 244, 65, 2, 99, 41, 31, 231, 199, 25, 32
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  , 255, 23, 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 231
  , 42, 38, 199, 25, 32, 29, 48, 244, 65, 2, 99, 41, 31, 255, 23, 231
  , 65, 2, 99, 41, 31, 231, 199, 25, 32, 255, 23, 42, 38, 29, 48, 244
  ]

input4 ∷ BS.ByteString
input4 = BS.pack
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
