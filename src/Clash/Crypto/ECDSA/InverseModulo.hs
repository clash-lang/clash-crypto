{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Clash.Crypto.ECDSA.InverseModulo where

import Clash.Prelude hiding (Mod)
import Clash.Crypto.ECDSA.Modulo (ModSize, Mod (..), unMod)
import Clash.Crypto.ECDSA.Utils (signedToUnsigned, unsignedToSigned)
import Data.Maybe (isJust, fromJust)

-- * Working implementations

-- |A streaming implementation of the Binary Euclidean Algorithm.
-- It computes an inverse modulo m.
-- `forall n. (bea @m n * n) `mod` (natToNum @m) == 1`
bea :: forall m dom. (KnownNat m, KnownDomain dom, HiddenClockResetEnable dom, 1 <= m) =>
 Signal dom (Maybe (Mod m)) ->
 Signal dom (Maybe (Mod m))
bea s = fmap (Mod @m) <$> mealy (~~>) BeaIdle s
 where
  (~~>) :: BeaState m -> Maybe (Mod m) -> (BeaState m, Maybe (Unsigned (ModSize m)))
  _ ~~> Just a = (BeaStart (bitCoerce $ resize $ unMod a, natToNum @m, 1, 0), Nothing)
  BeaIdle ~~> Nothing = (BeaIdle, Nothing)
  BeaStart (u, v, x, y) ~~> Nothing =
   let state = if u /= 1 && v /= 1 then BeaUMod2 (u, v, x, y) else BeaEnd (u, v, x, y)
   in (state, Nothing)
  BeaUMod2 (u, v, x, y) ~~> Nothing =
   if lsb u == low then
    let u' = u `shiftR` 1
        x' = if lsb x == low then x `shiftR` 1 else (x + natToNum @m) `shiftR` 1
    in (BeaUMod2 (u', v, resize x', y), Nothing)
   else (BeaVMod2 (u, v, x, y), Nothing)
  BeaVMod2 (u, v, x, y) ~~> Nothing =
   if lsb v == low then
    let v' = v `shiftR` 1
        y' = if lsb y == low then y `shiftR` 1 else (y + natToNum @m) `shiftR` 1
    in (BeaVMod2 (u, v', x, resize y'), Nothing)
   else (BeaCompare (u, v, x, y), Nothing)
  BeaCompare (u, v, x, y) ~~> Nothing =
   if u >= v then
    let u' = (u - v)
        x' = (x - y)
    in (BeaModU (resize u', v, resize x', y), Nothing)
   else
    let v' = (v - u)
        y' = (y - x)
    in (BeaModV (u, resize v', x, resize y'), Nothing)
  BeaModU (u, v, x, y) ~~> Nothing =
   let res = specialMod u in
   if isJust res then (BeaModU (fromJust res, v, x, y), Nothing) else (BeaModX (u, v, x, y), Nothing)
  BeaModX (u, v, x, y) ~~> Nothing =
   let res = specialMod x in
   if isJust res then (BeaModX (u, v, fromJust res, y), Nothing) else (BeaStart (u, v, x, y), Nothing)
  BeaModV (u, v, x, y) ~~> Nothing =
   let res = specialMod v in
   if isJust res then (BeaModV (u, fromJust res, x, y), Nothing) else (BeaModY (u, v, x, y), Nothing)
  BeaModY (u, v, x, y) ~~> Nothing =
   let res = specialMod y in
   if isJust res then (BeaModY (u, v, x, fromJust res), Nothing) else (BeaStart (u, v, x, y), Nothing)
  BeaEnd (u, _, x, y) ~~> Nothing =
   if u == 1
    then (BeaIdle, Just $ signedToUnsigned $ resize x)
    else (BeaIdle, Just $ signedToUnsigned $ resize y)
  specialMod val =
   if val <= natToNum @m then
    if val < 0 then Just $ val + natToNum @m else Nothing
   else Just $ val - natToNum @m

data BeaState (m :: Nat) =
 BeaIdle
 | BeaStart (Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2))
 | BeaUMod2 (Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2))
 | BeaVMod2 (Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2))
 | BeaCompare (Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2))
 | BeaModU (Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2))
 | BeaModV (Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2))
 | BeaModX (Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2))
 | BeaModY (Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2))
 | BeaEnd (Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2), Signed (ModSize m * 2))
 
 deriving (Generic, NFDataX, Show)

-- Combinatorial variant useful for testing against

-- Not synthesizeable.
inverseModulo_ :: forall len.
  KnownNat len => Unsigned len -> Unsigned len -> Maybe (Unsigned len)
inverseModulo_ _ 0 = Just 0
inverseModulo_ _ 1 = Just 1
inverseModulo_ a z = fmap (signedToUnsigned . (`mod` unsignedToSigned a)) $
  inverseModuloTmp (unsignedToSigned a) (unsignedToSigned z) 0 1

inverseModuloTmp :: forall len. KnownNat len =>
  Signed len -> Signed len -> Signed len -> Signed len -> Maybe (Signed len)
-- Success
inverseModuloTmp 1 0 y2 _ = Just y2
inverseModuloTmp _ 0 _ _ = Nothing -- Failure of some kind
inverseModuloTmp i j y2 y1 = inverseModuloTmp j reminder y1 y
 where
    (quotient, reminder) = quotRem i j
    y = y2 - (y1 * quotient)
