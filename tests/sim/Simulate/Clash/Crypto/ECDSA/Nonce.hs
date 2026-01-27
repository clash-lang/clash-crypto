module Simulate.Clash.Crypto.ECDSA.Nonce (tastyTests) where

import Clash.Prelude

import Test.Tasty
import Test.Tasty.Hedgehog
import Hedgehog
import qualified Hedgehog.Range as Range
import qualified Hedgehog.Gen as Gen

import qualified Crypto.Hash as Spec
import qualified Crypto.PubKey.ECC.ECDSA as Spec
import qualified Crypto.PubKey.ECC.Types as Spec
import Clash.Signal.DataStream
import qualified Data.ByteString as BS
import qualified Data.List as List
import Clash.Signal.Channel
import Clash.Crypto.ECDSA.DeterministicNonce
import Clash.Crypto.Hash.SHA
import Data.Maybe (catMaybes, listToMaybe, fromMaybe)
import qualified Clash.Crypto.Calculator.Modulo as M
import Clash.Crypto.Calculator.ISA (SecP256ModPrime, SecP256OrdPrime)

tastyTests ∷ TestTree
tastyTests = testGroup "Test.Clash.Crypto.ECDSA.Nonce" $
  [
    localOption (HedgehogShrinkLimit (Just 2))
    $ localOption (HedgehogTestLimit (Just 20))
    $ testProperty "Nonce generation" $ property $ do
      message <- forAll $ Gen.bytes (Range.linear 100 1000)
      pK      <- forAll
       $ Gen.integral (Range.linear 1 (natToNum @SecP256ModPrime - 1))
      let refDig = Spec.hash @_ @Spec.SHA256 message
          pKref  = Spec.PrivateKey (Spec.getCurveByName Spec.SEC_p256r1) pK
          ref = Spec.deterministicNonce Spec.SHA256 pKref refDig
              $ Just . fromInteger
          impl = withClockResetEnable clockGen resetGen enableGen
               $ runNonce (datastreamFromBS message) (fromInteger pK)
      ref === impl
  ]

runNonce ∷ HiddenClockResetEnable System ⇒
 DataStream System () (Index 8) (BitVector 8) →
 BitVector 256 →
 M.Mod SecP256OrdPrime
runNonce message pk
  = fromMaybe (error "Should contain an element") $ listToMaybe $ catMaybes
  $ sample @System $ newsfeed result
 where
  (result, rst) = deriveNonce SecP256OrdPrime SHA256 message pkC
  -- A small circuit that outputs the private key.
  pkC = head <$> pk2
  pk2 = mux rst (pure $ bitCoerce pk)
      $ flip rotateLeftS d1 <$> register (bitCoerce pk) pk2

datastreamFromBS ∷ BS.ByteString → DataStream dom () (Index 8) (BitVector 8)
datastreamFromBS = datastreamFromBV . fmap bitCoerce . BS.unpack

datastreamFromBV ∷ [BitVector 8] → DataStream dom () (Index 8) (BitVector 8)
datastreamFromBV bvs
 = fromList $ Idle : Idle : (listFromBV () 0  bvs <> List.repeat Idle)

listFromBV ∷  a → b → [BitVector 8] → [Frame a b (BitVector 8)]
listFromBV start end bvs
 = case List.unsnoc bvs of
    Nothing          → []
    Just (ys, y)     → case List.uncons ys of
        Nothing      → [End end y]
        Just (z, zs) → [Start start z]
                    <> List.concatMap (\x → [Middle x]) zs
                    <> [End end y]
