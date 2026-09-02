{-|
Module      : Clash.Crypto.Hash.SHA3.Streaming.Streaming
Copyright   : Copyright © 2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Streaming based hashing implementation of FIPS 202.
-}
{-# LANGUAGE MagicHash #-}
module Clash.Crypto.Hash.SHA3.Streaming.Streaming (sha3) where

import Clash.Prelude

import Language.Haskell.Unicode
import GHC.TypeNats.Proof

import Clash.Signal.DataStream (DataStream)
import Clash.Signal.Channel (Channel)
import Data.Constraint.Nat.Extra
  (KeepsPositiveIfMultiple, CancelMultiple, SubOfLTIsPos, SubOfPosIsLT, DDiv)
import Clash.Crypto.Hash.SHA3.Types
import Clash.Crypto.Hash.SHA3.Properties
    (KnownSHA3(..), SHA3Facts(SHA3Facts), SuffixLen)
import Clash.Crypto.Hash.SHA3.Functions.Permutations
  (rnd6, reverseBitsInByte, reverseBitsInBytes)
import Clash.Crypto.Hash.SHA3.Streaming.Padding (pad)
import Clash.Crypto.Hash.SHA3.Streaming.Sponge (spongeController)

-- | Streaming based implementation for the hashing algorithms defined
-- in FIPS 202.
-- This circuit implements the SHA3 hashing functions
-- on a streamed input.
sha3# ∷
  ∀ (n ∷ Nat) (dom ∷ Domain).
  (KnownNat n, HiddenClockResetEnable dom, 1 ≤ n) ⇒
  ∀ (alg ∷ SHA3) → KnownSHA3 alg ⇒
  (AlgRate alg `Mod` n ~ 0, 25 ≤ AlgRate alg `Div` n, SuffixLen alg < n) ⇒
  DataStream dom () (Index n) (BitVector n) →
  Channel dom (BitVector (MessageDigestSize alg))
sha3# alg
  | SHA3Facts ← knownSHA3 alg
  , Rewrite ← using @(SubOfLTIsPos (AlgStateSize alg) (AlgCapacity alg))
  , Rewrite ← using @(SubOfPosIsLT (AlgStateSize alg) (AlgCapacity alg))
  , Rewrite ← using @(KeepsPositiveIfMultiple (AlgRate alg) n)
  , Rewrite ← using @(CancelMultiple (AlgRate alg) n)
  = spongeController
        @n @dom
        @(AlgStateL alg) @(MessageDigestSize alg) (AlgRate alg)
        absorbFunction
    . pad @n @dom alg
  where absorbFunction state ir = rnd6 state ir

-- | Streaming based implementation for the hashing algorithms defined
-- in FIPS 202.
-- This circuit implements the SHA3 hashing functions
-- on a streamed input of bytes. In the output bytes,
-- the right-most bit is the msb.
sha3 ∷
  ∀ (dom ∷ Domain).
  HiddenClockResetEnable dom ⇒
  ∀ (alg ∷ SHA3) → (KnownSHA3 alg, SuffixLen alg < 8) ⇒
  DataStream dom () (Index 8) (BitVector 8) →
  Channel dom (Vec (MessageDigestSize alg `DDiv` 8) (BitVector 8))
sha3 alg input
  | SHA3Facts ← knownSHA3 alg
  , Rewrite ← using @(CancelMultiple (MessageDigestSize alg) 8)
  = b2h <$> sha3# @8 alg (h2b <$> input)
 where
  h2b frame = reverseBitsInByte <$> frame
  b2h dgst = reverseBitsInBytes dgst
