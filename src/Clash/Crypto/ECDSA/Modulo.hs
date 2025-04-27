{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingStrategies #-}

module Clash.Crypto.ECDSA.Modulo where

import Clash.Prelude hiding (Mod)
import Clash.Crypto.ECDSA.Utils
import Data.Bifunctor (Bifunctor(bimap))

-- * Useful types

type ModSize n = CLog 2 (n + 1)

newtype Mod (n :: Nat) = Mod (Index n)
 deriving (Show, Eq, Generic, Ord) deriving anyclass NFDataX

type Prime n = Mod n

unMod :: Mod n -> Index n
unMod (Mod s) = s

createMod :: forall n. (KnownNat n, 1 <= n) => Index n -> Mod n
createMod = Mod

-- Instances for Mod.
instance (KnownNat n, 1 <= n) => Enum (Mod n) where
 toEnum :: Int -> Mod n
 toEnum = fromIntegral
 fromEnum :: Mod n -> Int
 fromEnum = fromIntegral . unMod

instance (KnownNat n, 1 <= n, Ord (Mod n)) => Real (Mod n) where
 toRational = toRational . unMod

instance (KnownNat n, 1 <= n, Num (Mod n), Enum (Mod n), Real (Mod n)) => Integral (Mod n)
 where
  quotRem :: KnownNat n => Mod n -> Mod n -> (Mod n, Mod n)
  quotRem (Mod i) (Mod j) = bimap Mod Mod $ quotRem i j
  toInteger :: KnownNat n => Mod n -> Integer
  toInteger (Mod i) = toInteger i

instance (KnownNat n, 1 <= n) => Num (Mod n) where
 (+) :: Mod n -> Mod n -> Mod n
 Mod a + Mod b = Mod $ satAdd SatWrap a b
 (-) :: Mod n -> Mod n -> Mod n
 Mod a - Mod b = Mod $ satSub SatWrap a b
 (*) :: Mod n -> Mod n -> Mod n
 Mod a * Mod b = Mod $ satMul SatWrap a b
 abs :: Mod n -> Mod n
 abs = id
 signum :: Mod n -> Mod n
 signum = const (Mod 1)
 fromInteger :: Integer -> Mod n
 fromInteger i = Mod $ fromInteger i

-- |A streaming implementation of the modulo operation.
-- This implementation is constant-time, as it runs in `shifts` operations.
computeModuloPos :: forall m len shifts dom.
 (ModSize m <= len, 1 <= m, KnownNat m, KnownNat len, KnownDomain dom,
  HiddenClockResetEnable dom, shifts ~ len - ModSize m, KnownNat shifts) =>
 Signal dom (Maybe (Unsigned len)) ->
 Signal dom (Maybe (Mod m))
computeModuloPos =
 fmap (fmap (Mod @m . bitCoerce . resize)) . mealy (~~>) Finished . fmap (fmap resize)
 where
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
