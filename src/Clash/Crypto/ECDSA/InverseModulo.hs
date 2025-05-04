module Clash.Crypto.ECDSA.InverseModulo (bea) where

import Clash.Prelude hiding (Mod)
import Clash.Crypto.ECDSA.Modulo (ModSize, Mod (..), unMod, createMod)
import Clash.Crypto.ECDSA.Utils (signedToUnsigned, unsignedToSigned)
import Data.Constraint (Dict (Dict))
import Unsafe.Coerce (unsafeCoerce)

-- * Working implementations

-- |A streaming implementation of the Binary Euclidean Algorithm.
-- It computes an inverse modulo m.
-- prop> forall n. (bea @m n * n) `mod` (natToNum @m) == 1
bea :: forall m dom. (KnownNat m, KnownDomain dom, HiddenClockResetEnable dom, 1 <= m) =>
 Signal dom Bool -> -- ^ Toggle line
 Signal dom (Mod m) ->
 Signal dom (Maybe (Mod m))
-- TODO: Make this into a lemma.
bea toggle s | Dict <- unsafeCoerce (Dict :: Dict (0 <= 0)) :: Dict (1 <= ModSize m) =
 let
  p = natToNum @m
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
    BeaModU ->
     let (state, r) = nextState u BeaModU BeaModX
     in (BeaRunning state r v x y, Nothing)
    BeaModX ->
     let (state, r) = nextState x BeaModX BeaStart
     in (BeaRunning state u v r y, Nothing)
    BeaModV ->
     let (state, r) = nextState v BeaModV BeaModY
     in (BeaRunning state u r x y, Nothing)
    BeaModY ->
     let (state, r) = nextState y BeaModY BeaStart
     in (BeaRunning state u v x r, Nothing)
    BeaEnd ->
     let result  = if u == 1 then x else y
         result' =
          Just . truncateB @_ @_ @(ModSize m - 1) $ signedToUnsigned $
          if result < 0 then result + p else result
     in (BeaIdle, result')
  nextState val state1 state2 = maybe (state2, val) (state1,) $
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
