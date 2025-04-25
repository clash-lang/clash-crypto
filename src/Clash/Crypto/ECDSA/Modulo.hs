{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.ECDSA.Modulo where

import Clash.Prelude hiding (Mod)
import Clash.Crypto.ECDSA.Utils
import Data.Bifunctor (Bifunctor(bimap))
import GHC.Num (integerToInt)

-- * Useful types

type ModSize n = CLog 2 (n + 1)

newtype Mod (n :: Nat) = Mod (Unsigned (ModSize n))
 deriving (Show, Eq, Generic, Ord, NFDataX)

type Prime n = Mod n

unMod :: Mod n -> Unsigned (ModSize n)
unMod (Mod s) = s

-- |Should not be used in synthesis for big numbers as it uses `mod` internally.
createMod :: forall n. (KnownNat n, 1 <= n) => Unsigned (ModSize n) -> Mod n
createMod u = Mod $ u `mod` (snatToNum (SNat :: SNat n))

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
 (+) = addMod @n
 (-) :: Mod n -> Mod n -> Mod n
 (-) = subMod @n
 (*) :: Mod n -> Mod n -> Mod n
 (*) = mulMod @n
 abs :: Mod n -> Mod n
 abs = id
 signum :: Mod n -> Mod n
 signum = const (Mod 1)
 fromInteger :: Integer -> Mod n
 fromInteger i = Mod $ resize $ s `mod` (snatToNum (SNat @n))
  where
   s :: Unsigned (ModSize n * 2)
   s = fromInteger i

subMod :: forall n. (KnownNat n, 1 <= n) => Mod n -> Mod n -> Mod n
subMod (Mod i) (Mod j)
 | j <= i = Mod $ i - j
 | otherwise = Mod $ truncateB $ (i_ + (natToNum @n)) - j_
  where
  i_, j_ :: Unsigned (ModSize n + 1)
  i_ = extend i
  j_ = extend j

addMod :: forall n. (KnownNat n, 1 <= n) => Mod n -> Mod n -> Mod n
addMod (Mod i) (Mod j) = Mod $ truncateB $
 if res < m then res else res - m
 where
  m = natToNum @n
  i_, j_ :: Unsigned (ModSize n + 1)
  i_ = extend i
  j_ = extend j
  res = (i_ + j_)

-- |This multiplication implementation shouldn't be used for large numbers.
mulMod :: forall n. (KnownNat n, 1 <= n) => Mod n -> Mod n -> Mod n
mulMod (Mod i) (Mod j) = Mod res
 where
  res = resize $ (i' * j') `mod` (natToNum @n)
  i',j' :: Unsigned (ModSize n * 2)
  i' = resize i
  j' = resize j

-- |A streaming implementation of the modulo operation.
computeModuloPos :: forall m len shifts dom.
 (ModSize m <= len, 1 <= m, KnownNat m, KnownNat len, KnownDomain dom,
  HiddenClockResetEnable dom, shifts ~ len - ModSize m, KnownNat shifts) =>
 Signal dom (Maybe (Unsigned len)) ->
 Signal dom (Maybe (Mod m))
computeModuloPos =
 (fmap $ fmap (Mod @m . resize)) . mealy (~~>) Finished . fmap (fmap resize)
 where
  maxShifts :: Index (shifts + 1)
  maxShifts = natToNum @shifts
  (~~>) :: ComputationState (Index (shifts + 1), Unsigned len) ->
   Maybe (Unsigned len) ->
   (ComputationState (Index (shifts + 1), Unsigned len), Maybe (Unsigned len))
  _ ~~> Just n = (Working (maxShifts, n), Nothing)
  Finished ~~> Nothing = (Finished, Nothing)
  Working (s, n) ~~> Nothing =
   let shiftedm :: Unsigned len
       shiftedm = natToNum @m `shiftL` (integerToInt $ toInteger s)
   in
   if n < shiftedm
    then if s == 0 then (Finished, Just n) else (Working (s - 1, n), Nothing)
    else (Working (s, n - shiftedm), Nothing)
