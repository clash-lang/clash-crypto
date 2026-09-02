{-|
Module      : Clash.Crypto.Hash.SHA3.Functions.Padding
Copyright   : Copyright © 2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

This modules contains definitions related to the padding rule pad10*1.
-}
module Clash.Crypto.Hash.SHA3.Functions.Padding where

import Clash.Prelude.Safe

import Language.Haskell.Unicode (type (≤))
import GHC.TypeNats.Proof (Rewrite (..), QED (using))

import Data.Constraint.Nat.Extra (ModBound)
import Clash.Crypto.Hash.SHA3.Types (Pad101Size, ReqZerosPadding)

-- | A BitVector that contains the padding
-- according to the pad10*1 algorithm of a message
-- of length m so that
-- @m + len(pad101 x m)@ is a positive multiple of @x@.
pad101 ∷
  ∀ (x ∷ Nat) → (KnownNat x, 1 ≤ x) ⇒
  ∀ (m ∷ Nat) → KnownNat m ⇒
  BitVector (Pad101Size x m)
pad101 x m
  | Rewrite ← using @(ModBound (m + 2) x)
  =     (0b1 ∷ BitVector 1)
    ++# (zeroBits ∷ BitVector (ReqZerosPadding x m))
    ++# (0b1 ∷ BitVector 1)
