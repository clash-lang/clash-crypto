{-|
Module      : Clash.Crypto.ECDSA.InverseModulo
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Implementations of inverse modulo algorithms.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}

module Clash.Crypto.ECDSA.InverseModulo
  ( Precomp
  , bea
  , divSteps
  , fastGcdSequential
  , fltCtmi
  , sictMiSequential
  , deriveSictPrecomp
  ) where

import Clash.Netlist.Util (orNothing)
import Clash.Prelude hiding (Mod)

import Control.Monad (guard)
import Data.Constraint.Nat.Extra (CLog2KeepsPositive)
import Data.Maybe (isJust, fromMaybe)
import Data.Type.Bool (If)
import GHC.TypeNats.Proof (Rewrite(..), using)

import qualified Data.Functor as F (unzip)
import qualified GHC.TypeLits as P (Mod)

import Clash.Crypto.ECDSA.InverseModulo.Internal
import Clash.Crypto.ECDSA.Fraction (HWFraction (HWFraction), shiftRFraction)
import Clash.Crypto.ECDSA.Karatsuba (karatsubaSequentialGated)
import Clash.Crypto.ECDSA.Modulo
  (ModSize, Mod (..), moduloShift, computeModuloUnsigned, computeModuloSigned)
import Clash.Crypto.ECDSA.Utils
  ( ComputationState, pattern Working, pattern Finished
  , signedToUnsigned, unsignedToSigned
  )

-- * Binary Euclidean Algorithm

-- | A streaming implementation of the Binary Euclidean Algorithm.
-- It computes the inverse of a positive integer modulo m.
--
-- prop> forall n. (bea @m n * n) `mod` (natToNum @m) == 1
bea :: forall m dom.
 (KnownNat m, KnownDomain dom, HiddenClockResetEnable dom, 2 <= m) =>
 Signal dom Bool -> -- ^ Toggle line
 Signal dom (Mod m) ->
 Signal dom (Maybe (Mod m))
bea toggle s | Rewrite <- using @(CLog2KeepsPositive m) =
 let
  p = natToNum @m
  (~~>) :: BeaState m ->
           Maybe (Mod m) ->
           (BeaState m, Maybe (Unsigned (ModSize m)))
  _ ~~> Just a =
   (BeaRunning BeaStart
    (extend @_ @_ @(ModSize m - 1) . unsignedToSigned . bitCoerce $ a)
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
  fmap bitCoerce <$> mealy (~~>) BeaIdle valueM

type BeaData m = Signed (ModSize m * 2)

data BeaMode
  =  BeaStart  |  BeaUMod2  |  BeaVMod2  |  BeaCompare  |  BeaModU
  |  BeaModV   |  BeaModX   |  BeaModY   |  BeaEnd
  deriving (Generic, NFDataX, Show)

data BeaState (m :: Nat)
  = BeaIdle
  | BeaRunning BeaMode (BeaData m) (BeaData m) (BeaData m) (BeaData m)
  deriving (Generic, NFDataX, Show)

-- * FastGCD

-- | Number of iterations for FastGCD based on the bitlength.
type Iterations (d :: Nat) =
 1 + If (d <=? 45) (Div (49 * d + 80 - 17) 17) (Div (49 * d + 57 - 17) 17)

type FastGCDIterations d = Iterations (ModSize d)

-- | Precomputed value used by FastGCD.
type Precomp (f :: Nat) =
 P.Mod (Div (f + 1) 2 ^ (FastGCDIterations f - 1)) f

type MulRegisterSize = 36
type GCDStreamingStages = 3

type DenMax m = FastGCDIterations m + 1

data FastGCDRecord len = FastGCD
 { remaining :: Index (len + 1)
 , delta     :: Signed (ModSize len + 1)
 , f         :: Signed (len + 1)
 , g         :: Signed (len + 1)
 , v         :: HWFraction (len + 1) len
 , r         :: HWFraction (len + 1) len
 } deriving (Generic, NFDataX)

type FastGCDState m = ComputationState (FastGCDRecord (FastGCDIterations m))

-- | A sequential implementation of the divSteps2 function described in
-- Bernstein/Yang's paper Fast constant-time gcd computation and modular
-- inversion.
divSteps :: forall m dom.
 (HiddenClockResetEnable dom, KnownNat m, KnownDomain dom, 1 <= m, 1 <= FastGCDIterations m,
  KnownNat (FastGCDIterations m), ModSize m <= FastGCDIterations m) =>
 Signal dom Bool -> -- ^ Toggle signal
 Signal dom (Unsigned (ModSize m)) ->
 Signal dom (Maybe (Signed (DenMax m), HWFraction (DenMax m) (FastGCDIterations m)))
divSteps toggle value = mealy (~~>) Finished valueM
  where
   toggleSwitched = toggle ./=. register False toggle
   valueM = mux toggleSwitched (Just <$> value) (pure Nothing)
   shuffle state@(FastGCD {..}) =
     if (delta <= 0) || (not . bitToBool . lsb $ g)
     then state
     else state { delta = negate delta, f = g, g = negate f, v = r, r = negate v }
   shifter state@(FastGCD {..}) =
    let
     (g1, r1) = if bitToBool . lsb $ g then (g + f, r + v) else (g, r)
    in state { remaining = remaining - 1, delta = delta + 1
             , g = shiftR g1 1, r = shiftRFraction r1 }
   (~~>) :: FastGCDState m ->
    Maybe (Unsigned (ModSize m)) ->
    (FastGCDState m, Maybe (Signed (DenMax m), HWFraction (DenMax m) (FastGCDIterations m)))
   Finished ~~> Nothing = (Finished, Nothing)
   Finished ~~> Just g  =
    (Working $ FastGCD maxBound 1 (natToNum @m) (unsignedToSigned . resize $ g) 0 1,
     Nothing)
   Working (FastGCD { remaining = 0, .. }) ~~> _ = (Finished, Just (f, v))
   Working state ~~> _ = (Working . shifter . shuffle $ state, Nothing)

-- | A sequential implementation for FastGCD. It shouldn't be used directly,
-- because better resource usage could be achieved by sharing subcomponents.
fastGcdSequential :: forall m dom.
 (KnownNat m, 1 <= m, KnownDomain dom, HiddenClockResetEnable dom, 1 <= Iterations m,
  ModSize m <= FastGCDIterations m) =>
 Signal dom Bool -> -- ^ Toggle signal
 Signal dom (Mod m) -> -- ^ Number to invert
 Signal dom (Maybe (Mod m))
fastGcdSequential toggle s =
  let
   -- Precomputed value for the algorithm.
   precomp :: Signal dom (Unsigned (ModSize m))
   precomp = pure $ natToNum @(Precomp m)
   divTransform (fu, HWFraction n val) =
    (if signum fu < 0 then negate val else val, maxBound - n - 1)
   -- 1. Compute divSteps.
   divResult = divSteps @m toggle $ bitCoerce <$> s
   (divFrac, divShifts) = unbundle $ F.unzip . fmap divTransform <$> divResult
   -- Keeping the shift in memory as we'll use it later on.
   shifts = mux (isJust <$> divShifts) (fromMaybe 0 <$> divShifts) $
    register 0 shifts
   -- 2. Compute the modulo of the outputted value.
   modFraction =
    liftA2 (\sign -> if sign == high then negate else id) <$> fuSign <*> tmpMod
   tmpMod = computeModuloUnsigned @m toggleModulo $
     register 0 $ maybe 0 signedToUnsigned <$> divFrac
   moduloShiftedFraction :: Signal dom (Maybe (Unsigned (ModSize m)))
   moduloShiftedFraction = fmap bitCoerce <$>
    moduloShift @m toggleShift (register 0 (fromMaybe 0 <$> modFraction)) shifts
   fuSign :: Signal dom (Maybe Bit)
   fuSign = register Nothing $ mux (isJust <$> divFrac) (fmap msb <$> divFrac) fuSign
   -- Toggles, since they all use registers, the input also need to be delayed.
   toggleKaratsuba, toggleLastMod, toggleModulo :: Signal dom Bool
   toggleModulo = register False $ (isJust <$> divFrac) ./=. toggleModulo
   toggleShift = register False $ (isJust <$> tmpMod) ./=. toggleShift
   toggleKaratsuba =
    register False $ (isJust <$> moduloShiftedFraction) ./=. toggleKaratsuba
   toggleLastMod = register False $ (isJust <$> karatsubaRes) ./=. toggleLastMod
   karatsubaRes = karatsubaSequentialGated @GCDStreamingStages @MulRegisterSize
    toggleKaratsuba (fromMaybe 0 <$> register Nothing moduloShiftedFraction) precomp
  in
   computeModuloUnsigned @m toggleLastMod $ fromMaybe 0 <$> register Nothing karatsubaRes

type FLTIterations m = ModSize (m - 2)

data FLTState t =
 FLTWaiting  |
 FLTSquare t |
 FLTMul t
 deriving (Generic, NFDataX, Show)

type FLTMode = Bool -- Square or Mul

-- | A working implementation of Inverse Modulo based on Fermat's Little
-- Theorem. Fine up to 256 bits, and only works with prime moduli.
fltCtmi :: forall m dom.
 (KnownNat m, 3 <= m, KnownDomain dom, HiddenClockResetEnable dom) =>
 Signal dom Bool -> -- ^ Toggle signal
 Signal dom (Mod m) -> -- ^ Number to invert
 Signal dom (Maybe (Mod m))
fltCtmi toggle value
 =
 let
  toggleSwitched = toggle ./=. register False toggle
  k :: Vec (ModSize (m - 2)) Bit
  k = reverse $ bv2v (natToNum @(m - 2) :: BitVector (ModSize (m - 2)))
  toggleModulo = register False $ (isJust <$> karatsubaMul) ./=. toggleModulo
  toggleMul = register False $ restart ./=. toggleMul
  karatsubaMul = karatsubaSequentialGated
   @GCDStreamingStages @MulRegisterSize @(ModSize m) @(ModSize m)
   toggleMul (bitCoerce <$> c) $ bitCoerce <$> mux switch value c
  moduloMul =
   computeModuloUnsigned @m toggleModulo $ register 0 $ fromMaybe 0 <$> karatsubaMul
  c = regMaybe 0
   $ (\m t v -> m <|> (guard t >> pure v))
       <$> moduloMul
       <*> toggleSwitched
       <*> value
  (switch, restart, end) =
   unbundle $ mealy (~~>) FLTWaiting $
   bundle (toggleSwitched, isJust <$> moduloMul)
  (~~>) :: FLTState (Index (FLTIterations m)) ->
   (Bool, Bool) -> -- (restart, got mul result)
   (FLTState (Index (FLTIterations m)), (FLTMode, Bool, Bool))
   -- (iterations, square/mul, restart, end)
  _ ~~> (True, _) = (FLTSquare maxBound, (False, True, False))
  FLTWaiting ~~> _ = (FLTWaiting, (False, False, False))
  FLTSquare 0 ~~> _ = (FLTWaiting, (False, False, True))
  FLTSquare remaining ~~> (_, True) =
   -- Check the i-th bit of k
   if bitToBool $ k !! (remaining - 1) then
    (FLTMul remaining, (True, True, False))
   else
    (FLTSquare $ remaining - 1, (False, True, False))
  FLTMul remaining ~~> (_, True) =
    (FLTSquare $ remaining - 1, (False, True, False))
  -- Waiting for a result.
  FLTSquare remaining ~~> _ =
   (FLTSquare remaining, (False, False, False))
  FLTMul remaining ~~> _ =
    (FLTMul remaining, (True, False, False))
 in orNothing <$> end <*> c

-- * SictMi

-- This algorithm comes from Jin and Miyaji's paper Short-Iteration
-- Constant-Time GCD and Modular inversion.

data SictMiRecord m = SictMi
 { remaining :: Index (SictIterations m + 1)
 , u         :: Signed (ModSize m + 1)
 , v         :: Signed (ModSize m + 1)
 , q         :: Signed (SictIterations m * 2 + 1)
 , r         :: Signed (SictIterations m * 2 + 1)
 } deriving (Generic, NFDataX, Show)

type SictMiState m = ComputationState (SictMiRecord m)

sictMiLoop :: forall m dom.
 (HiddenClockResetEnable dom, KnownNat m, KnownDomain dom, 1 <= m) =>
 Signal dom Bool -> -- ^ Toggle signal
 Signal dom (Unsigned (ModSize m)) ->
 Signal dom (Maybe (Signed (SictIterations m * 2 + 1)))
sictMiLoop toggle value = mealy (~~>) Finished valueM
  where
   toggleSwitched = toggle ./=. register False toggle
   valueM = orNothing <$> toggleSwitched <*> value
   firstOp s z x y = (if s `xor` z then x else 0) + (if s && z then y else negate y)
   secondOp s z x y = (if s then x else 0) +
    if z then (if s then negate y else y) else (if s then 0 else y `shiftL` 1)
   initialize input = SictMi maxBound input (natToNum @m) 0 1
   mainCalc (SictMi {..}) =
    let
     s  = bitToBool . lsb $ u
     z  = bitToBool . lsb $ v
     t1 = firstOp s z v u
     t2 = secondOp s z v u `shiftR` 1
     t3 = firstOp s z q r `shiftL` 1
     t4 = secondOp s z q r
    in (remaining, t1, t2, t3, t4)
   shuffle (remaining, t1, t2, t3, t4) =
    let
     s      = t2 >= t1
     (v, u) = if s then (t2, t1) else (t1, t2)
     (q, r) = if s then (t4, t3) else (t3, t4)
    in SictMi (remaining - 1) u v q r
   (~~>) :: SictMiState m ->
    Maybe (Unsigned (ModSize m)) ->
    (SictMiState m, Maybe (Signed (SictIterations m * 2 + 1)))
   Finished ~~> Nothing = (Finished, Nothing)
   Finished ~~> Just g  =
    (Working $ initialize $ resize $ unsignedToSigned g,
     Nothing)
   Working (SictMi { remaining = 0, .. }) ~~> _ = (Finished, Just q)
   Working state ~~> _ = (Working . shuffle . mainCalc $ state, Nothing)

sictMiSequential :: forall m dom.
 (KnownNat m, 1 <= m, KnownDomain dom, HiddenClockResetEnable dom, SictPrecompKnownNat m,
  1 <= m - 2 * ModSize m, 2 * ModSize m <= m, 1 <= 2 * ModSize m * (m - 1)) =>
 Signal dom Bool -> -- ^ Toggle signal
 Signal dom (Mod m) -> -- ^ Number to invert
 Signal dom (Maybe (Mod m))
sictMiSequential toggle s
 = let
   -- Precomputed value for the algorithm.
   precomp :: Signal dom (Unsigned (ModSize m))
   precomp = pure $ getSictPrecomp @m
   divResult = sictMiLoop @m toggle $ bitCoerce <$> s
   modResult = computeModuloSigned @m @(SictIterations m * 2) toggleModulo $ fromMaybe 0 <$> register Nothing divResult
   -- Toggles, since they all use registers, the input also need to be delayed.
   toggleKaratsuba, toggleLastMod, toggleModulo :: Signal dom Bool
   toggleModulo = register False $ (isJust <$> divResult) ./=. toggleModulo
   toggleKaratsuba =
    register False $ (isJust <$> modResult) ./=. toggleKaratsuba
   toggleLastMod = register False $ (isJust <$> karatsubaRes) ./=. toggleLastMod
   karatsubaRes = karatsubaSequentialGated @GCDStreamingStages @MulRegisterSize
    toggleKaratsuba (bitCoerce . fromMaybe 0 <$> register Nothing modResult) precomp
  in
   computeModuloUnsigned @m toggleLastMod $ fromMaybe 0 <$> register Nothing karatsubaRes
