{-|
Module      : Clash.Crypto.ECDSA.InverseModulo
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Implementations of inverse modulo algorithms.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.ECDSA.InverseModulo
 (bea, divSteps, fastGcdSequential, Precomp)
where

import Clash.Crypto.ECDSA.Lemmas (lemmaModSize)
import Clash.Crypto.ECDSA.Modulo
 (ModSize, Mod (..), unMod, createMod, moduloShift, computeModuloPos)
import Clash.Crypto.ECDSA.Utils (signedToUnsigned, unsignedToSigned)
import Clash.Prelude hiding (Mod)
import Data.Constraint (Dict (Dict))
import qualified GHC.TypeLits as P
import Data.Type.Bool (If)
import Clash.Crypto.ECDSA.Fraction (HWFraction (HWFraction), shiftRFraction)
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Functor as F
import Data.Maybe (isJust, fromMaybe)
import Clash.Crypto.ECDSA.Karatsuba (karatsubaSequentialGated)

-- * Binary Euclidean Algorithm

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

-- * FastGCD

-- |Number of iterations for FastGCD based on the bitlength.
type Iterations (d :: Nat) =
 If (d <=? 45) (Div (49 * d + 80) 17) (Div (49 * d + 57) 17)

-- |Precomputed value used by FastGCD.
type Precomp (f :: Nat) =
 P.Mod ((Div (f + 1) 2) ^ (Iterations (ModSize f) - 1)) f

type MulRegisterSize = 36
type GCDStreamingStages = 3

type DenMax m = Iterations (ModSize m) + 1

data FGCDComputationState t =
 Finished     |
 Start t      |
 Step t
 deriving (Generic, NFDataX, Show)

type FastGCDState m len =
 FGCDComputationState (Index (len + 1), Signed (ModSize len + 1), Signed (len + 1),
  Signed (len + 1), HWFraction (DenMax m) len, HWFraction (DenMax m) len)

-- |A sequential implementation of the divSteps2 function described in
-- Bernstein/Yang's paper Fast constant-time gcd computation and modular
-- inversion.
divSteps :: forall m len dom.
 (HiddenClockResetEnable dom, KnownNat m, KnownDomain dom, 1 <= m,
  KnownNat len, len ~ Iterations (ModSize m), 1 <= len) =>
 Signal dom Bool -> -- ^ Toggle signal
 Signal dom (Unsigned (ModSize m)) ->
 Signal dom (Maybe (Signed (len + 1), HWFraction (DenMax m) len))
divSteps toggle value = mealy (~~>) Finished valueM
  where
   toggleSwitched = toggle ./=. register False toggle
   valueM = mux toggleSwitched (Just <$> value) (pure Nothing)
   (~~>) :: FastGCDState m len ->
    Maybe (Unsigned (ModSize m)) ->
    (FastGCDState m len, Maybe (Signed (len + 1), HWFraction (DenMax m) len))
   Finished ~~> Nothing = (Finished, Nothing)
   Finished ~~> Just g  =
    (Start (maxBound, 1,
     unsignedToSigned $ natToNum @m,
     unsignedToSigned $ resize g, 0, 1), Nothing)
   Start (0, _, f, _, v, _) ~~> _ = (Finished, Just (f, v))
   Start (left, delta, f, g, v, r) ~~> _ =
    if mask0 then
     (Step (left, delta, f, g, v, r), Nothing)
    else
     (Step (left, negate delta, g, negate f, r, negate v), Nothing)
    where mask0 = (delta <= 0) || (g .&. 1 == 0)
   Step (left, delta, f, g, v, r) ~~> _ =
     (Start (left - 1, delta + 1, f, g'', v, r''), Nothing)
     where
      (g', r') = if g0 then (g + f, r + v) else (g, r)
      g'' = shiftR g' 1
      r'' = shiftRFraction r'
      g0 = bitToBool $ lsb g .&. 1

-- |A sequential implementation for FastGCD. It shouldn't be used directly,
-- because better resource usage could be achieved by sharing subcomponents.
fastGcdSequential :: forall m dom.
 (KnownNat m, 1 <= m, KnownDomain dom, HiddenClockResetEnable dom) =>
 Signal dom Bool -> -- ^ Toggle signal
 Signal dom (Mod m) ->
 Signal dom (Maybe (Mod m))
fastGcdSequential toggle s
 | Dict <- lemmaModSize @m
 , Dict <- lemmaIterations @(ModSize m)
 , Dict <- lemmaGeneralizedIterations @(ModSize m)
 = let
   -- Precomputed value for the algorithm.
   precomp :: Signal dom (Unsigned (ModSize m))
   precomp = pure $ natToNum @(Precomp m)
   divTransform (fu, HWFraction n val) =
    (if signum fu < 0 then negate val else val, maxBound - n - 1)
   -- 1. Compute divSteps.
   divResult = divSteps @m toggle $ bitCoerce . unMod <$> s
   (divFrac, divShifts) = unbundle $ F.unzip <$> fmap divTransform <$> divResult
   -- Keeping the shift in memory as we'll use it later on.
   shifts = mux (isJust <$> divShifts) (fromMaybe 0 <$> divShifts) $
    register 0 shifts
   -- 2. Compute the modulo of the outputted value.
   modFraction = fromMaybe 0 <$>
    (fmap (\(v,sign) -> if sign == high then negate v else v)
    <$> (liftA2 (,) <$> tmpMod <*> fuSign))
   tmpMod = computeModuloPos @m toggleModulo $
     register 0 $ fromMaybe 0 . fmap signedToUnsigned <$> divFrac
   moduloShiftedFraction :: Signal dom (Maybe (Unsigned (ModSize m)))
   -- TODO: Rewrite in a cleaner manner.
   moduloShiftedFraction = fmap (bitCoerce . unMod) <$>
    (moduloShift @m toggleShift $ (,) <$>
     (register 0 modFraction) <*>
     shifts)
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
   computeModuloPos @m toggleLastMod $ fromMaybe 0 <$> register Nothing karatsubaRes

-- * Lemmas

lemmaIterations :: forall d. (KnownNat d, 1 <= d) => Dict (1 <= Iterations d)
lemmaIterations = unsafeCoerce (Dict :: Dict (0 <= 0))

lemmaGeneralizedIterations :: forall d. (KnownNat d, 1 <= d) => Dict (d <= Iterations d)
lemmaGeneralizedIterations = unsafeCoerce (Dict :: Dict (0 <= 0))
