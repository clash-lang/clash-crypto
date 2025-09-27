{-|
Module      : Clash.Crypto.ECDSA.Modulo
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Types and algorithms for modulo integers.
-}

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.ECDSA.Modulo
  ( Mod(..)
  , Prime
  , ModSize
  , unMod
  , createMod
  , computeModuloUnsigned
  , computeModuloSigned
  , moduloShift
  ) where

import Clash.Crypto.ECDSA.Utils
import Clash.Num.Wrapping (Wrapping (Wrapping))
import Clash.Prelude hiding (Mod)
import Clash.Signal.Channel

import Data.Coerce (coerce)
import Language.Haskell.Unicode (type (≤))

-- * Useful types

type ModSize n = CLog 2 n

newtype Mod (n ∷ Nat) = Mod (Wrapping (Index n))
 deriving (Show, Eq, Generic, Ord) deriving newtype NFDataX

deriving newtype instance (KnownNat n, 1 ≤ n) ⇒ Num (Mod n)
deriving newtype instance (KnownNat n, 1 ≤ n) ⇒ Enum (Mod n)
deriving newtype instance (KnownNat n, 1 ≤ n) ⇒ Real (Mod n)
deriving newtype instance (KnownNat n, 1 ≤ n) ⇒ Integral (Mod n)
deriving newtype instance (KnownNat n, 1 ≤ n) ⇒ Bits (Mod n)
deriving newtype instance (KnownNat n, 1 ≤ n) ⇒ BitPack (Mod n)

type Prime n = Mod n

unMod ∷ Mod n → Index n
unMod = coerce

createMod ∷ ∀ n. (KnownNat n, 1 ≤ n) ⇒ Index n → Mod n
createMod = coerce

-- | A streaming implementation of the modulo operation using long division
-- in a binary base. Works on unsigned values.
-- This implementation is constant-time, as it runs in `shifts` operations.
computeModuloUnsigned ∷
  ∀ m len shifts dom.
  ( KnownNat m, KnownNat len, KnownNat shifts, HiddenClockResetEnable dom
  , 1 ≤ m, ModSize m ≤ len, shifts ~ len - ModSize m
  ) ⇒
  Channel dom (Unsigned len) →
  Channel dom (Mod m)
computeModuloUnsigned = enhance put get compute
 where
  put n = (n, maxBound ∷ Index (shifts + 1))
  get _ = Mod @m . bitCoerce . resize . fst
  compute _ (n, j) = ((subIfGE n $ shiftedm j, satPred SatBound j), j > 0)
  shiftedm = shiftL (natToNum @m) . fromEnum

-- | A streaming implementation of the modulo operation using long division
-- in a binary base. Works on signed values.
-- This implementation is constant-time, as it runs in `shifts` operations.
computeModuloSigned ∷
  ∀ m len shifts dom.
  ( KnownNat m, KnownNat len,  KnownNat shifts, HiddenClockResetEnable dom
  , 1 ≤ m, ModSize m ≤ len, shifts ~ len - ModSize m
  ) ⇒
  Channel dom (Signed (len + 1)) →
  Channel dom (Mod m)
computeModuloSigned = enhance put get compute
 where
  put n = (n, maxBound ∷ Index (shifts + 2))
  get _ = Mod @m . bitCoerce . resize . signedToUnsigned . fst
  compute _ (n, j) = ((next n j, if j > 0 then j - 1 else j), j > 0)
  -- ^ using `satPred SatBound j` instead does not work here because of
  -- https://github.com/clash-lang/ghc-typelits-natnormalise/issues/94
  next n j
    | j == maxBound = n + if n < 0 then shiftedm (j - 1) else 0
    | otherwise     = subIfGE n $ shiftedm j

  shiftedm = shiftL (natToNum @m) . fromEnum

-- | Shifts a number to the left and computes the modulo as it shifts it.
-- Used by FastGCD.
-- Takes constant time, taking `maxShifts` cycles.
-- That input will be constant for the max number of shifts.
moduloShift ∷
  ∀ m maxShifts dom.
  ( KnownNat m, KnownNat maxShifts, HiddenClockResetEnable dom
  , 1 ≤ m, 1 ≤ maxShifts
  ) ⇒
  Channel dom (Mod m, Index maxShifts) →
  -- ^ Number to shift, number of shifts
  Channel dom (Mod m)
moduloShift = enhance put get compute
 where
  put (n, _) = (extend $ bitCoerce n, maxBound ∷ Index maxShifts)
  get _ = bitCoerce . truncateB . fst
  compute (_, s) (n, j)
    | j > 0     = Computing (next s n j, satPred SatBound j)
    | otherwise = Releasing (n, j)
  next s n j
    | s < j     = n ∷ Unsigned (ModSize m + 1)
    | otherwise = subIfGE (n `shiftL` 1) $ natToNum @m

-- | Substracts the second argument from the first one, but only if
-- the first argument is larger than second one. Otherwise, the first
-- argument is returned unchanged.
subIfGE ∷ (Num a, Ord a) ⇒ a → a → a
subIfGE x y
  | x >= y    = x - y
  | otherwise = x
