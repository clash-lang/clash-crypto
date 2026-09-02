{-|
Module      : Clash.Crypto.Hash.SHA3.State
Copyright   : Copyright © 2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Definition of the state type and basic util functions.
-}
{-# LANGUAGE MagicHash #-}

module Clash.Crypto.Hash.SHA3.State where

import Clash.Prelude.Safe hiding (type (^))

import GHC.TypeNats.Proof (type (^))
import Language.Haskell.Unicode (type (≤))

-- | State Width as a function of ℓ.
type StateWidth l = 2 ^ l

-- | State Size as a function of ℓ.
type StateSize l = 25 * (StateWidth l)

-- | Internal representation of state as a 3D array.
type State l = Vec 5 (Vec 5 (BitVector (StateWidth l)))

-- | Definition of the State as a vector type.
type StateArray (l ∷ Nat) = BitVector (StateSize l)

-- | Constraints for ℓ.
type KnownStateL l = (KnownNat l, l ≤ 6)

-- | Util function to transform a vector to a state array.
toState ∷
  ∀ (l ∷ Nat). KnownStateL l ⇒
  StateArray l →
  State l
toState = transpose . bitCoerce

-- | Util function to transform a state array to a vector.
toArray ∷
  ∀ (l ∷ Nat). KnownStateL l ⇒
  State l →
  StateArray l
toArray = bitCoerce . transpose
