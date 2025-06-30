{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
module Test.Clash.Crypto.MAC.HMAC where

import Clash.Prelude
import Data.Maybe
import qualified Data.List as List

import Test.Tasty
import Test.Tasty.Hedgehog

import Clash.Crypto.MAC.HMAC
import Clash.Crypto.Hash.SHA

import Test.Clash.Crypto.Hash.SHA

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Clash.Hedgehog.Sized.BitVector as Gen (genDefinedBitVector)

-- Reference implementation
import qualified Crypto.MAC.HMAC as Spec
import qualified Data.ByteString as BS

type HmacChunkSize = 8
type NumKeyChunks alg = Div (BlockSize alg) HmacChunkSize

-- Test parameters
numTestCycles, maxMsgSizeForTesting :: Int
numTestCycles = 4000
maxMsgSizeForTesting = 499

tastyTests :: TestTree
tastyTests =
  testGroup "Test.Clash.Crypto.MAC.HMAC"
    [ testProperty "Test hmac against reference implementation" testHmacHedgehog
    ]

type Alg = SHA256
testHmacHedgehog :: Property
testHmacHedgehog =
  property $ do
    testKey <- forAll
      $ Gen.list (Range.constant 1 (natToNum @(NumKeyChunks Alg))) Gen.genDefinedBitVector
    testMsg <- forAll
      $ Gen.list (Range.constant 1 maxMsgSizeForTesting) Gen.genDefinedBitVector
    let testInput = (testKey, testMsg)
    (hmacImpl @Alg testInput === hmacRefImpl @Alg testInput)


hmacImpl ::
  forall (alg :: SHA) m.
  KnownSHA alg =>
  SuitableDivisorForHMAC 8 alg m =>
  ([BitVector 8], [BitVector 8]) ->
  BS.ByteString
hmacImpl (keyData, msgData)
  | SHAFacts _ <- knownSHA @alg
  = let
    keyInput = List.map (\b -> (Just b, True)) keyData
    msgInput = List.map (\b -> (Just b, False)) msgData

    hmacTestInput :: [(Maybe (BitVector 8), Bool)]
    hmacTestInput =
      -- Skip over reset
      List.replicate 3 (Nothing, True)
      -- Test data
      <> keyInput
      -- Note: The circuit needs at most `2*(BlockSize alg / n)+c` cycles
      -- to pad the key, where `n` in this case is 8 and `c` is a small constant
      -- potentially introduced by registers etc. `c=3` should be sufficient.
      <> List.replicate 300 (Nothing, False)
      <> msgInput
      <> List.repeat (Nothing, True)

    (hmacTestData, hmacTestIsKey) = unbundle $ fromList hmacTestInput

    output :: Vec (MessageDigestSize alg `Div` 8) (BitVector 8)
    output =
      unconcatBitVector#
        $ maybe 0 fst
        $ List.uncons
        $ catMaybes
        $ sampleN @System numTestCycles
        $ withClockResetEnable clockGen resetGen enableGen
        $ hmac @alg hmacTestIsKey hmacTestData

    outputBS = BS.pack $ toList $ unpack <$> output
  in outputBS


hmacRefImpl ::
  forall (alg :: SHA).
  (KnownSHA alg, CryptoHash alg) =>
  ([BitVector 8], [BitVector 8]) ->
  BS.ByteString
hmacRefImpl (keyData, msgData)
  | SHAFacts alg <- knownSHA @alg
  = let
    key = BS.pack $ List.map bitCoerce keyData
    msg = BS.pack $ List.map bitCoerce msgData

    referenceOutput :: BS.ByteString
    referenceOutput =
      Spec.hmac (cryptoHash alg) (natToNum @(BlockSize alg `Div` 8)) key msg
  in referenceOutput

