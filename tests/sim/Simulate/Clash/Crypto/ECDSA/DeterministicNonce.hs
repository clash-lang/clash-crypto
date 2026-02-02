module Simulate.Clash.Crypto.ECDSA.DeterministicNonce (tastyTests) where

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
import qualified Data.List as List
import Clash.Signal.Channel
import Clash.Crypto.ECDSA.DeterministicNonce
import Clash.Crypto.Hash.SHA
import Data.Maybe (catMaybes, listToMaybe, fromMaybe)
import qualified Clash.Crypto.Calculator.Modulo as M
import Clash.Crypto.Calculator.ISA (SecP256ModPrime, SecP256OrdPrime)
import qualified Data.ByteArray as Memory
import qualified Clash.Sized.Vector as Vec

tastyTests ∷ TestTree
tastyTests = testGroup "Test.Clash.Crypto.ECDSA.Nonce"
  [ testProperty "Nonce generation" $ property $ do
      message <- forAll $ Gen.bytes (Range.linear 1 1000)
      pK      <- forAll
       $ Gen.integral (Range.linear 1 (natToNum @SecP256ModPrime - 1))
      let refDig = Spec.hash @_ @Spec.SHA256 message
          h = Memory.unpack refDig
          p = Vec.toList $ bitCoerce
            $ fromInteger @(Unsigned (MessageDigestSize SHA256)) pK
          pKref = Spec.PrivateKey (Spec.getCurveByName Spec.SEC_p256r1) pK
          ref = Spec.deterministicNonce Spec.SHA256 pKref refDig
              $ Just . fromInteger
          impl = withClockResetEnable clockGen resetGen enableGen
               $ generateNonce (datastreamFromBV $ p <> (bitCoerce <$> h))
      ref === impl
  ]

generateNonce ∷ HiddenClockResetEnable System ⇒
 DataStream System () () (BitVector 8) →
 M.Mod SecP256OrdPrime
generateNonce message
  = fromMaybe (error "No response received") $ listToMaybe $ catMaybes
  $ sample @System $ newsfeed result
 where
  (result, hmacOutput) = deriveNonce SecP256OrdPrime SHA256 message hmacInput
  hmacInput = sha SHA256 hmacOutput

datastreamFromBV ∷ [BitVector 8] → DataStream dom () () (BitVector 8)
datastreamFromBV bvs
 = fromList $ Idle : Idle : listFromBV () ()  bvs <> List.repeat Idle

listFromBV ∷  a → b → [BitVector 8] → [Frame a b (BitVector 8)]
listFromBV start end bvs
 = case List.unsnoc bvs of
    Nothing          → []
    Just (ys, y)     → case List.uncons ys of
        Nothing      → [End end y]
        Just (z, zs) → [Start start z]
                    <> List.concatMap (\x → [Middle x]) zs
                    <> [End end y]
