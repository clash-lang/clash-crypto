{-|
Module      : Clash.Crypto.ECDSA.InverseModulo
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Implementations of inverse modulo algorithms.
-}

module Clash.Crypto.ECDSA.InverseModulo (bea) where

import Clash.Crypto.ECDSA.Lemmas (lemmaModSize)
import Clash.Crypto.ECDSA.Modulo (ModSize, Mod (..), unMod, createMod)
import Clash.Crypto.ECDSA.Utils (signedToUnsigned, unsignedToSigned)
import Clash.Prelude hiding (Mod)
import Data.Constraint (Dict (Dict))

-- * Working implementations

-- |A streaming implementation of the Binary Euclidean Algorithm.
-- It computes the inverse of a positive integer modulo m.
-- 
-- prop> forall n. (bea @m n * n) `mod` (natToNum @m) == 1
bea :: forall m dom.
 (KnownNat m, KnownDomain dom, HiddenClockResetEnable dom, 1 <= m) =>
 Signal dom Bool -> -- ^ Toggle line
 Signal dom (Mod m) ->
 Signal dom (Maybe (Mod m))
bea toggle s | Dict <- lemmaModSize @m =
 let
  p = natToNum @m
  (~~>) :: BeaState m ->
           Maybe (Mod m) ->
           (BeaState m, Maybe (Unsigned (ModSize m)))
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
     let (state, u', x') = computeMod2 u x BeaUMod2 BeaVMod2
     in (BeaRunning state u' v x' y, Nothing)
    BeaVMod2 ->
     let (state, v', y') = computeMod2 v y BeaVMod2 BeaCompare
     in (BeaRunning state u v' x y', Nothing)
    BeaCompare ->
     if u >= v then
      let u' = u - v
          x' = x - y
      in (BeaRunning BeaModU u' v x' y, Nothing)
     else
      let v' = v - u
          y' = y - x
      in (BeaRunning BeaModV u v' x y', Nothing)
    BeaModU ->
     let (state, r) = computeMod u BeaModU BeaModX
     in (BeaRunning state r v x y, Nothing)
    BeaModX ->
     let (state, r) = computeMod x BeaModX BeaStart
     in (BeaRunning state u v r y, Nothing)
    BeaModV ->
     let (state, r) = computeMod v BeaModV BeaModY
     in (BeaRunning state u r x y, Nothing)
    BeaModY ->
     let (state, r) = computeMod y BeaModY BeaStart
     in (BeaRunning state u v x r, Nothing)
    BeaEnd ->
     let result  = if u == 1 then x else y
         result' =
          Just . truncateB @_ @_ @(ModSize m - 1) $ signedToUnsigned $
          if result < 0 then result + p else result
     in (BeaIdle, result')
  computeMod2 val1 val2 state1 state2 =
   if lsb val1 == low then
    let val1' = val1 `shiftR` 1
        val2' = (if lsb val2 == low then val2 else val2 + p) `shiftR` 1
    in (state1, val1', val2')
   else (state2, val1, val2)
  computeMod val state1 state2 = maybe (state2, val) (state1,) $
   if val <= natToNum @m then
    if val < 0 then Just $ val + natToNum @m else Nothing
   else Just $ val - natToNum @m
  toggleSwitched = toggle ./=. register False toggle
  valueM = mux toggleSwitched (Just <$> s) (pure Nothing)
 in
  fmap (createMod . bitCoerce) <$> mealy (~~>) BeaIdle valueM

type BeaData m = Signed (ModSize m * 2)

data BeaMode
  =  BeaStart  |  BeaUMod2  |  BeaVMod2  |  BeaCompare  |  BeaModU
  |  BeaModV   |  BeaModX   |  BeaModY   |  BeaEnd
  deriving (Generic, NFDataX, Show)

data BeaState (m :: Nat)
  = BeaIdle
  | BeaRunning BeaMode (BeaData m) (BeaData m) (BeaData m) (BeaData m)
  deriving (Generic, NFDataX, Show)
