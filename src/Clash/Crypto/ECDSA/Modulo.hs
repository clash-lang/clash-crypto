{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}

module Clash.Crypto.ECDSA.Modulo
 (Mod(..), computeModuloPos, Prime, unMod, createMod, ModSize)
where

import Clash.Prelude hiding (Mod)
import Clash.Crypto.ECDSA.Utils
import Clash.Num.Wrapping (Wrapping (fromWrapping), toWrapping)
import Data.Coerce (coerce)

-- * Useful types

type ModSize n = CLog 2 n

newtype Mod (n :: Nat) = Mod (Wrapping (Index n))
 deriving (Show, Eq, Generic, Ord) deriving newtype NFDataX

deriving newtype instance (KnownNat n, 1 <= n) => Num (Mod n)
deriving newtype instance (KnownNat n, 1 <= n) => Enum (Mod n)
deriving newtype instance (KnownNat n, 1 <= n) => Real (Mod n)
deriving newtype instance (KnownNat n, 1 <= n) => Integral (Mod n)

type Prime n = Mod n

unMod :: Mod n -> Index n
unMod = fromWrapping . coerce

createMod :: forall n. (KnownNat n, 1 <= n) => Index n -> Mod n
createMod = coerce . toWrapping

-- |A streaming implementation of the modulo operation using long division
-- in a binary base
-- This implementation is constant-time, as it runs in `shifts` operations.
computeModuloPos :: forall m len shifts dom.
 (ModSize m <= len, 1 <= m, KnownNat m, KnownNat len, KnownDomain dom,
  HiddenClockResetEnable dom, shifts ~ len - ModSize m, KnownNat shifts) =>
 Signal dom Bool -> -- ^ Toggle signal
 Signal dom (Unsigned len) ->
 Signal dom (Maybe (Mod m))
computeModuloPos toggle value =
 fmap (Mod @m . bitCoerce . resize) <$> mealy (~~>) Finished valueM
 where
  toggleSwitched = toggle ./=. register False toggle
  valueM = mux toggleSwitched (Just . resize <$> value) (pure Nothing)
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
   let shiftedm :: Unsigned len
       shiftedm = m `shiftL` fromEnum s
   in (Working (s - 1, if n < shiftedm then n else n - shiftedm), Nothing)
