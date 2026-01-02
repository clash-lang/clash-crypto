{-|
Module      : Simulate.Clash.Crypto.MAC.HMAC
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Simulation tests for 'Clash.Crypto.MAC.HMAC'.
-}

{-# LANGUAGE MagicHash #-}

module Simulate.Clash.Crypto.MAC.HMAC where

import Clash.Prelude
import Clash.Signal.Channel
import Clash.Signal.DataStream

import Data.Constraint.Nat.Extra (CancelMultiple)
import Data.Maybe
import GHC.TypeNats.Proof (Rewrite(..), using)
import qualified Data.List as List
import Language.Haskell.Unicode (type (≤))

import Test.Tasty
import Test.Tasty.Hedgehog

import Clash.Crypto.MAC.HMAC
import Clash.Crypto.Hash.SHA

import Simulate.Clash.Crypto.Hash.SHA

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

-- Reference implementation
import qualified Crypto.Hash as Spec
import qualified Crypto.MAC.HMAC as Spec
import qualified Data.ByteArray as Memory
import qualified Data.ByteString as BS
import Data.ByteString (ByteString)

tastyTests ∷ TestTree
tastyTests =
  testGroup "Test.Clash.Crypto.MAC.HMAC"
    [ testProperty "Contiguous Input"     $ testHmacHedgehog SHA256 True
    , testProperty "Non-contiguous Input" $ testHmacHedgehog SHA256 False
    ]

testHmacHedgehog ∷
  ∀ (alg ∷ SHA) →
  (KnownSHA alg, CryptoHash alg, Spec.HashAlgorithm (CryptoToHash alg)) ⇒
  (8 ≤ BlockSize alg, Mod (BlockSize alg) 8 ~ 0) ⇒
  Bool → Property
testHmacHedgehog alg contiguous
  | SHAFacts ← knownSHA alg
  = property $ do
    let n = natToNum @(BlockSize alg `Div` 8)
        m = 499 -- max message size
        genSpacings (BS.length → j)
          | contiguous = pure $ List.replicate j 0
          | otherwise  = Gen.list (Range.singleton j)
                       $ Gen.integral @_ @Int $ Range.linear 1 100
    testKey ← forAll $ Gen.bytes $ Range.linear 1 n
    testMsg ← forAll $ Gen.bytes $ Range.linear 1 m
    keySpacings ← forAll $ genSpacings testKey
    msgSpacings ← forAll $ genSpacings testMsg
    let testInput = (testKey, testMsg)
        ref = hmacRefImpl alg testInput
        dut = hmacImpl alg (keySpacings, msgSpacings) testInput
    ref === dut

showLn ∷ ShowX a ⇒ [a] → String
showLn = List.concatMap ((<> "\n") . showX)

hmacImpl ∷
  ∀ (alg ∷ SHA) → (KnownSHA alg, CryptoHash alg) ⇒
  (8 ≤ BlockSize alg, Mod (BlockSize alg) 8 ~ 0) ⇒
  ([Int], [Int]) →
  (ByteString, ByteString) →
  ByteString
hmacImpl alg (keySpacings, msgSpacings) (keyData, msgData)
  | SHAFacts ← knownSHA alg
  , Rewrite  ← using @(CancelMultiple (MessageDigestSize alg) 8)
  = let
      addSpacings xs
        = List.concatMap (\(j, x) → x : List.replicate j NoData)
        . List.zip xs

      restructure = (Middle . bitCoerce <$>) . BS.unpack

      keyInput = addSpacings keySpacings $
        case restructure keyData of
          Middle x : xr → Start (toEnum $ BS.length keyData) x : xr
          y → y

      msgSpacings' = List.reverse $ case List.reverse msgSpacings of
        []     → []
        _ : xr → 0 : xr

      msgInput = addSpacings msgSpacings' $ List.reverse $
        case List.reverse $ restructure msgData of
          Middle x : xr → End () x : xr
          y → y

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

      hmacTestInput ∷
        [Frame (Index ((BlockSize alg `Div` 8) + 1)) () (BitVector 8)]
      hmacTestInput =
        -- Skip over reset
        List.replicate 3 Idle
        -- Test data
        <> keyInput
        -- we need to send exactly `BlockSize alg` many bits before
        -- sending the msg
        <> List.replicate (n - BS.length keyData) (Middle 0xFF)
        <> msgInput
        <> List.repeat Idle

      output ∷ Vec (MessageDigestSize alg `Div` 8) (BitVector 8)
      output
        = unconcatBitVector#
        $ maybe (error "No response received.") fst
        $ List.uncons
        $ catMaybes
        $ sampleN @System requiredSamples
        $ newsfeed
        $ withClockResetEnable clockGen resetGen enableGen
        $ hmac alg
        $ fromList hmacTestInput
    in
      BS.pack $ toList $ unpack <$> output

hmacRefImpl ∷
  ∀ (alg ∷ SHA) ->
  (KnownSHA alg, CryptoHash alg, Spec.HashAlgorithm (CryptoToHash alg)) ⇒
  (ByteString, ByteString) → ByteString
hmacRefImpl alg
  | SHAFacts <- knownSHA alg
  = BS.pack . Memory.unpack . Spec.hmacGetDigest
  . uncurry (Spec.hmac @_ @_ @(CryptoToHash alg))
