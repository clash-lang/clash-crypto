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
  , computeModuloPrime
  , moduloShift
  , splitNumber
  ) where

import Clash.Crypto.ECDSA.Utils
import Clash.Num.Wrapping (Wrapping (Wrapping))
import Clash.Prelude hiding (Mod, SNat (..))
import Clash.Signal.Channel

import Data.Coerce (coerce)
import Language.Haskell.Unicode (type (≤))

import qualified Data.List as L (replicate)
import Data.Type.Equality
import GHC.TypeLits (SNat)

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
  put n = (signedToUnsigned n, maxBound ∷ Index (shifts + 1), msb n)
  get _ (a, _, sign) = Mod @m . bitCoerce . resize $
   if bitToBool sign && a /= 0 then natToNum @m - a else a
  compute _ (n, j, sign) =
   ((subIfGE n $ shiftedm j, satPred SatBound j, sign), j > 0)
  shiftedm = shiftL (natToNum @m) . fromEnum

-- Add a step from the ECDSA document.
-- Has the restriction than the number must be < p^2.
splitNumber :: Unsigned (ModSize Q * 2) -> Signed (ModSize Q + 7)
splitNumber a = t + s1 * 2 + s2 * 2 + s3 + s4 - id1 - id2 - id3 - id4
 where
  vA :: Vec 16 (Unsigned 32)
  vA = reverse $ bitCoerce a -- To have the right indices.
  fromIndices :: Vec 8 (Maybe (Index 16)) -> Signed 263
  fromIndices = extend . unsignedToSigned . bitCoerce . map (maybe 0 (vA !!))
  t,s1,s2,s3,s4,id1,id2,id3,id4 :: Signed 263
  t  = fromIndices $(listToVecTH $ fmap Just [7,6,5,4,3,2,1,0 :: Index 16])
  s1 = fromIndices $(listToVecTH $ fmap Just [15,14,13,12,11 :: Index 16] <> L.replicate 3 Nothing)
  s2 = fromIndices $(listToVecTH $ Nothing : (fmap Just [15,14,13,12 :: Index 16]) <> L.replicate 3 Nothing)
  s3 = fromIndices $(listToVecTH $ fmap Just [15,14 :: Index 16] <> L.replicate 3 Nothing <> fmap Just [10,9,8])
  s4 = fromIndices $(listToVecTH $ fmap Just [8,13,15,14,13,11,10,9 :: Index 16])
  id1 = fromIndices $(listToVecTH $ fmap Just [10,8 :: Index 16] <> L.replicate 3 Nothing <> fmap Just [13,12,11])
  id2 = fromIndices $(listToVecTH $ fmap Just [11,9 :: Index 16] <> L.replicate 2 Nothing <> fmap Just [15,14,13,12])
  id3 = fromIndices $(listToVecTH $ [Just (12 :: Index 16), Nothing] <> fmap Just [10,9,8,15,14,13])
  id4 = fromIndices $(listToVecTH $ [Just (13 :: Index 16), Nothing] <> fmap Just [11,10,9] <> [Nothing] <> fmap Just [15,14])

-- TODO: Factor it out.
type Q = 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

-- Number has to be smaller than m ^ 2.
computeModuloPrime ::
  ∀ m dom. ( KnownNat m, HiddenClockResetEnable dom, 1 ≤ m ) ⇒
  Channel dom (Unsigned (ModSize m * 2)) →
  Channel dom (Mod m)
computeModuloPrime =
  case testEquality (natSing :: SNat m) (natSing :: SNat Q) of
    Just Refl -> computeModuloSigned @Q . fmap splitNumber . delayC
    Nothing   -> computeModuloUnsigned @m

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
