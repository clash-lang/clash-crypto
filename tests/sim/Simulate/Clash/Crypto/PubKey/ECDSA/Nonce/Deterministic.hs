{-|
Module      : Simulate.Clash.Crypto.PubKey.ECDSA.Nonce.Deterministic
Copyright   : Copyright © 2025-2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Simulation tests for 'Clash.Crypto.PubKey.ECDSA.Nonce.Deterministic'.
-}

module Simulate.Clash.Crypto.PubKey.ECDSA.Nonce.Deterministic
  ( tastyTests
  ) where

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
import Clash.Crypto.PubKey.ECDSA.Nonce.Deterministic (deriveNonce)
import Clash.Crypto.Hash.SHA
import Data.Maybe (catMaybes, listToMaybe, fromMaybe)
import Clash.Crypto.Calculator.Modulo (ℤₘ)
import Clash.Crypto.Calculator.ISA (SecP256ModPrime, SecP256OrdPrime)
import qualified Data.ByteArray as Memory
import qualified Clash.Sized.Vector as Vec

tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.PubKey.ECDSA.Nonce.Deterministic"
  [ testProperty "Nonce Generation" $ property $ do
      let m = natToNum @(SecP256ModPrime - 1)
      message <- forAll $ Gen.bytes (Range.linear 1 1000)
      pK <- forAll $ Gen.integral (Range.linear 1 m)
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

generateNonce ∷
  HiddenClockResetEnable System ⇒
  DataStream System () () (BitVector 8) →
  ℤₘ SecP256OrdPrime
generateNonce message
  = fromMaybe (error "No response received") $ listToMaybe $ catMaybes
  $ sample @System $ newsfeed result
 where
  (result, hmacOutput) = deriveNonce SecP256OrdPrime SHA256 message hmacInput
  hmacInput = sha SHA256 hmacOutput

datastreamFromBV ∷ [BitVector 8] → DataStream dom () () (BitVector 8)
datastreamFromBV bvs
  = fromList $ Idle : Idle : listFromBV () () bvs <> List.repeat Idle

listFromBV ∷  a → b → [BitVector 8] → [Frame a b (BitVector 8)]
listFromBV start end bvs = case List.unsnoc bvs of
  Nothing      → []
  Just (ys, y) → case List.uncons ys of
    Nothing      → [End end y]
    Just (z, zs) → [Start start z]
                <> List.concatMap (\x → [Middle x]) zs
                <> [End end y]
