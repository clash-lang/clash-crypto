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
{-# LANGUAGE DerivingVia #-}

module Clash.Crypto.ECDSA.Modulo
 (Mod(..), computeModuloUnsigned, Prime, unMod, createMod, ModSize,
  moduloShift, computeModuloSigned)
where

import Clash.Crypto.ECDSA.Utils
import Clash.Prelude hiding (Mod)
import Clash.Num.Wrapping (Wrapping (Wrapping))
import Data.Coerce (coerce)
import Clash.Netlist.Util (orNothing)

-- * Useful types

type ModSize n = CLog 2 n

newtype Mod (n :: Nat) = Mod (Wrapping (Index n))
 deriving (Show, Eq, Generic, Ord) deriving newtype NFDataX

deriving newtype instance (KnownNat n, 1 <= n) => Num (Mod n)
deriving newtype instance (KnownNat n, 1 <= n) => Enum (Mod n)
deriving newtype instance (KnownNat n, 1 <= n) => Real (Mod n)
deriving newtype instance (KnownNat n, 1 <= n) => Integral (Mod n)
deriving newtype instance (KnownNat n, 1 <= n) => Bits (Mod n)
deriving newtype instance (KnownNat n, 1 <= n) => BitPack (Mod n)

type Prime n = Mod n

unMod :: Mod n -> Index n
unMod = coerce

createMod :: forall n. (KnownNat n, 1 <= n) => Index n -> Mod n
createMod = coerce

-- |A streaming implementation of the modulo operation using long division
-- in a binary base. Works on unsigned values.
-- This implementation is constant-time, as it runs in `shifts` operations.
computeModuloUnsigned :: forall m len shifts dom.
 (ModSize m <= len, 1 <= m, KnownNat m, KnownNat len, KnownDomain dom,
  HiddenClockResetEnable dom, shifts ~ len - ModSize m, KnownNat shifts) =>
 Signal dom Bool -> -- ^ Toggle signal
 Signal dom (Unsigned len) ->
 Signal dom (Maybe (Mod m))
computeModuloUnsigned toggle value =
 fmap (Mod @m . bitCoerce . resize) <$> mealy (~~>) Finished valueM
 where
  toggleSwitched = toggle ./=. register False toggle
  valueM = orNothing <$> toggleSwitched <*> value
  m :: Unsigned len
  m = natToNum @m
  maxShifts :: Index (shifts + 1)
  maxShifts = natToNum @shifts
  (~~>) :: ComputationState (Index (shifts + 1), Unsigned len) ->
   Maybe (Unsigned len) ->
   (ComputationState (Index (shifts + 1), Unsigned len), Maybe (Unsigned len))
  _ ~~> Just n = (Working (maxShifts, n), Nothing)
  Finished ~~> Nothing = (Finished, Nothing)
  Working (0, n) ~~> Nothing =
   (Finished, if n < m then Just n else Just $ n - m)
  Working (s, n) ~~> Nothing =
   let shiftedm = m `shiftL` fromEnum s
   in (Working (s - 1, if n < shiftedm then n else n - shiftedm), Nothing)

-- |A streaming implementation of the modulo operation using long division
-- in a binary base. Works on signed values.
-- This implementation is constant-time, as it runs in `shifts` operations.
computeModuloSigned :: forall m len shifts dom.
 (ModSize m <= len, 1 <= m, KnownNat m, KnownNat len, KnownDomain dom,
  HiddenClockResetEnable dom, shifts ~ len - ModSize m, KnownNat shifts) =>
 Signal dom Bool -> -- ^ Toggle signal
 Signal dom (Signed (len + 1)) ->
 Signal dom (Maybe (Mod m))
computeModuloSigned toggle value =
 fmap (Mod @m . bitCoerce . resize) <$> mealy (~~>) Finished valueM
 where
  toggleSwitched = toggle ./=. register False toggle
  valueM = orNothing <$> toggleSwitched <*> value
  m :: Signed (len + 1)
  m = natToNum @m
  (~~>) :: ComputationState (Bool, Index (shifts + 1), Signed (len + 1)) ->
   Maybe (Signed (len + 1)) ->
   (ComputationState (Bool, Index (shifts + 1), Signed (len + 1)), Maybe (Unsigned len))
  _ ~~> Just n = (Working (False, maxBound, n), Nothing)
  Finished ~~> Nothing = (Finished, Nothing)
  -- First state.
  Working (False, s, n) ~~> Nothing =
   let shiftedm = m `shiftL` fromEnum s
   in (Working (True, s, if n < 0 then n + shiftedm else n), Nothing)
  Working (True, 0, n) ~~> Nothing =
   (Finished, Just $ signedToUnsigned $ if n < m then n else n - m)
  Working (True, s, n) ~~> Nothing =
   let shiftedm = m `shiftL` fromEnum s
   in (Working (True, s - 1, if n < shiftedm then n else n - shiftedm), Nothing)

-- |Shifts a number to the left and computes the modulo as it shifts it.
-- Used by FastGCD.
-- Takes constant time, taking `maxShifts` cycles.
-- That input will be constant for the max number of shifts.
moduloShift :: forall m maxShifts dom.
 (KnownNat m, KnownDomain dom, HiddenClockResetEnable dom,
  KnownNat maxShifts, 1 <= m) =>
 Signal dom Bool ->
 -- ^ Toggle signal
 Signal dom (Mod m) ->
 -- ^ Number to shift
 Signal dom (Index maxShifts) ->
 -- ^ Number of shifts, assumes stability of this value
 Signal dom (Maybe (Mod m))
moduloShift toggle value shifts = mealy (~~>) Finished $ bundle (valueM, shifts)
 where
  toggleSwitched = toggle ./=. register False toggle
  valueM = orNothing <$> toggleSwitched <*> value
  (~~>) ::
   ComputationState (Unsigned (ModSize m + 1), Index maxShifts) ->
   (Maybe (Mod m), Index maxShifts) ->
   (ComputationState (Unsigned (ModSize m + 1), Index maxShifts), Maybe (Mod m))
  _ ~~> (Just n, _) = (Working (extend . bitCoerce $ n, maxBound), Nothing)
  Finished ~~> (Nothing, _) = (Finished, Nothing)
  Working (n, 0) ~~> (Nothing, _) = (Finished, Just . bitCoerce . truncateB $ n)
  Working (n, shiftsRemaining) ~~> (Nothing, totalShifts) =
   let
    r = n `shiftL` 1
    res
      | totalShifts < shiftsRemaining = n
      | r < natToNum @m = r
      | otherwise = r - natToNum @m
   in
    (Working (res, shiftsRemaining - 1), Nothing)
