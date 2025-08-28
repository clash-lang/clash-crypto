{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
module Test.Clash.Crypto.MAC.HMAC where

import Clash.Prelude
import Data.Constraint.Nat.Extra (CancelMultiple)
import Data.Maybe
import GHC.TypeNats.Proof (Rewrite(..), using)
import qualified Data.List as List

import Test.Tasty
import Test.Tasty.Hedgehog

import Clash.Crypto.MAC.HMAC
import Clash.Crypto.Hash.SHA

import Test.Clash.Crypto.Hash.SHA

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

-- Reference implementation
import qualified Crypto.MAC.HMAC as Spec
import qualified Data.ByteString as BS
import Data.ByteString (ByteString)

tastyTests :: TestTree
tastyTests =
  testGroup "Test.Clash.Crypto.MAC.HMAC"
    [ testProperty "Contiguous Input"     $ testHmacHedgehog @SHA256 True
    , testProperty "Non-contiguous Input" $ testHmacHedgehog @SHA256 False
    ]

testHmacHedgehog ::
  forall (alg :: SHA).
  ( KnownSHA alg, CryptoHash alg
  , 8 <= BlockSize alg, Mod (BlockSize alg) 8 ~ 0
  ) =>
  Bool -> Property
testHmacHedgehog contiguous
  | SHAFacts _ <- knownSHA @alg
  = property $ do
    let n = natToNum @(BlockSize alg `Div` 8)
        m = 499 -- max message size
        genSpacings (BS.length -> j)
          | contiguous = pure $ List.replicate j 0
          | otherwise  = Gen.list (Range.singleton j)
                       $ Gen.integral @_ @Int $ Range.linear 1 100
    isKeyI <- forAll Gen.bool
    testKey <- forAll $ Gen.bytes $ Range.linear 1 n
    testMsg <- forAll $ Gen.bytes $ Range.linear 1 m
    keySpacings <- forAll $ genSpacings testKey
    msgSpacings <- forAll $ genSpacings testMsg
    let testInput = (testKey, testMsg)
    (===) (hmacRefImpl @alg testInput)
          (hmacImpl @alg isKeyI (keySpacings, msgSpacings) testInput)

hmacImpl ::
  forall (alg :: SHA).
  (KnownSHA alg, 8 <= BlockSize alg, Mod (BlockSize alg) 8 ~ 0) =>
  Bool ->
  ([Int], [Int]) ->
  (ByteString, ByteString) ->
  ByteString
hmacImpl isKeyI (keySpacings, msgSpacings) (keyData, msgData)
  | SHAFacts _ <- knownSHA @alg
  , Rewrite ← using @(CancelMultiple (MessageDigestSize alg) 8)
  = let
      addSpacings xs
        = List.concatMap (\(j, x) -> x : List.replicate j (fst x, Nothing))
        . List.zip xs

      restructure b
        = ((b, )  . Just . bitCoerce <$>) . BS.unpack

      keyInput = addSpacings keySpacings $ restructure True keyData
      msgInput = addSpacings msgSpacings $ restructure False msgData

      n = natToNum @(BlockSize alg `Div` 8)
      m = BS.length keyData + BS.length msgData
      i = List.length keyInput + List.length msgInput + n - BS.length keyData
      sc = max n $ natToNum @(ScheduleCount alg)

      -- over-approximation (for keeping the calculation simple)
      requiredSamples           -- cycles for
        = i                     --   > passing all input
        + sc * (m `div` sc + 3) --   > computing the inner hash
        + 2 * n                 --   > passing key and digest of the outer hash
        + 5 * sc                --   > computing the outer hash

      hmacTestInput :: [(Bool, Maybe (BitVector 8))]
      hmacTestInput =
        -- Skip over reset
        List.replicate 3 (isKeyI, Nothing)
        -- Test data
        <> keyInput
        -- we need to send exactly `BlockSize alg` many bits before
        -- sending the msg
        <> List.replicate (n - BS.length keyData) (False, Just 0xFF)
        <> msgInput
        <> List.repeat (True, Nothing)

      output :: Vec (MessageDigestSize alg `Div` 8) (BitVector 8)
      output
        = unconcatBitVector#
        $ maybe (error "No response received.") fst
        $ List.uncons
        $ catMaybes
        $ sampleN @System requiredSamples
        $ withClockResetEnable clockGen resetGen enableGen
        $ uncurry (hmac @alg)
        $ unbundle
        $ fromList hmacTestInput
    in
      BS.pack $ toList $ unpack <$> output

hmacRefImpl ::
  forall (alg :: SHA).
  (KnownSHA alg, CryptoHash alg) =>
  (ByteString, ByteString) ->
  ByteString
hmacRefImpl (key, msg)
  | SHAFacts alg <- knownSHA @alg
  = Spec.hmac (cryptoHash alg) (natToNum @(BlockSize alg `Div` 8)) key msg
