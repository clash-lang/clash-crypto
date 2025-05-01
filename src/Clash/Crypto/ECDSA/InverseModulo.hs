{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Clash.Crypto.ECDSA.InverseModulo where

import Clash.Prelude hiding (Mod)
import Clash.Crypto.ECDSA.Modulo (ModSize, Mod (..), unMod, createMod)
import Clash.Crypto.ECDSA.Utils (signedToUnsigned, unsignedToSigned)
import Data.Constraint (Dict (Dict))
import Unsafe.Coerce (unsafeCoerce)

-- * Working implementations

-- |A streaming implementation of the Binary Euclidean Algorithm.
-- It computes an inverse modulo m.
-- `forall n. (bea @m n * n) `mod` (natToNum @m) == 1`
bea :: forall m dom. (KnownNat m, KnownDomain dom, HiddenClockResetEnable dom, 1 <= m) =>
 Signal dom (Maybe (Mod m)) ->
 Signal dom (Maybe (Mod m))
-- TODO: Make this into a lemma.
bea s | Dict <- unsafeCoerce (Dict :: Dict (0 <= 0)) :: Dict (1 <= ModSize m)
 =
 let
  (~~>) :: BeaState m -> Maybe (Mod m) -> (BeaState m, Maybe (Unsigned (ModSize m)))
  _ ~~> Just a =
   (BeaRunning BeaStart
    (extend @_ @_ @(ModSize m - 1) $ unsignedToSigned $ bitCoerce $ unMod a)
    (natToNum @m) 1 0, Nothing)
  BeaIdle ~~> Nothing = (BeaIdle, Nothing)
  BeaRunning mode u v x y ~~> Nothing =
   case mode of
    BeaStart ->
     let state = if u /= 1 && v /= 1 then BeaUMod2 else BeaEnd
     in (BeaRunning state u v x y, Nothing)
   -- Refactor these
    BeaUMod2 ->
     if lsb u == low then
      let u' = u `shiftR` 1
          x' = (if lsb x == low then x else x + p) `shiftR` 1
      in (BeaRunning BeaUMod2 u' v x' y, Nothing)
     else (BeaRunning BeaVMod2 u v x y, Nothing)
    BeaVMod2 ->
     if lsb v == low then
       let v' = v `shiftR` 1
           y' = (if lsb y == low then y else y + p) `shiftR` 1
       in (BeaRunning BeaVMod2 u v' x y', Nothing)
     else (BeaRunning BeaCompare u v x y, Nothing)
    BeaCompare ->
     if u >= v then
      let u' = u - v
          x' = x - y
      in (BeaRunning BeaModU u' v x' y, Nothing)
     else
      let v' = v - u
          y' = y - x
      in (BeaRunning BeaModV u v' x y', Nothing)
    -- Refactor these
    BeaModU ->
     let (state, r) = tmp u BeaModU BeaModX
     in (BeaRunning state r v x y, Nothing)
    BeaModX ->
     let (state, r) = tmp x BeaModX BeaStart
     in (BeaRunning state u v r y, Nothing)
    BeaModV ->
     let (state, r) = tmp v BeaModV BeaModY
     in (BeaRunning state u r x y, Nothing)
    BeaModY ->
     let (state, r) = tmp y BeaModY BeaStart
     in (BeaRunning state u v x r, Nothing)
    BeaEnd ->
     let result  = if u == 1 then x else y
         result' =
          Just . truncateB @_ @_ @(ModSize m - 1) $ signedToUnsigned $
          if result < 0 then result + p else result
     in (BeaIdle, result')
  p = natToNum @m
  tmp val state1 state2 =
   let res = specialMod val
   in case res of
    Left  res' -> (state1, res')
    Right res' -> (state2, res')
  specialMod :: BeaData m -> Either (BeaData m) (BeaData m)
  specialMod val =
   if val <= natToNum @m then
    if val < 0 then Left $ val + natToNum @m else Right val
   else Left $ val - natToNum @m
 in
  fmap (createMod . bitCoerce) <$> mealy (~~>) BeaIdle s

type BeaData m = Signed (ModSize m * 2)

data BeaMode
  =  BeaStart  |  BeaUMod2  |  BeaVMod2  |  BeaCompare  |  BeaModU
  |  BeaModV   |  BeaModX   |  BeaModY   |  BeaEnd
  deriving (Generic, NFDataX, Show)

data BeaState (m :: Nat)
  = BeaIdle
  | BeaRunning BeaMode (BeaData m) (BeaData m) (BeaData m) (BeaData m)
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
