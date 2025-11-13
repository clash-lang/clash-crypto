{-|
Module      : Clash.Crypto.ECDSA.InverseModulo
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Implementations of inverse modulo algorithms.
-}

{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}

module Clash.Crypto.ECDSA.InverseModulo
  ( Precomp
  , bea
  , fastGcdSequential
  , fltCtmi
  , sictMiSequential
  , deriveSictPrecomp
  , splitNumber
  ) where

import Clash.Prelude hiding (Mod)
import Clash.Signal.Channel
import Clash.Signal.Extra (apWhen)

import Data.Constraint.Nat.Extra (CLog2KeepsPositive)
import GHC.TypeNats.Proof (Rewrite(..), using, If)
import Language.Haskell.Unicode (type (≤))

import qualified GHC.TypeLits as P (Mod)

import Clash.Crypto.ECDSA.InverseModulo.Internal
import Clash.Crypto.ECDSA.Fraction (HWFraction (HWFraction), shiftRFraction)
import Clash.Crypto.ECDSA.Karatsuba (karatsubaSequentialGated)
import Clash.Crypto.ECDSA.Modulo
  (ModSize, Mod (..), moduloShift, computeModuloUnsigned, computeModuloSigned)
import Clash.Crypto.ECDSA.Utils (unsignedToSigned, signedToUnsigned)

import qualified Data.List as L

-- * Binary Euclidean Algorithm

-- | A streaming implementation of the Binary Euclidean Algorithm.
-- It computes the inverse of a positive integer modulo m.
--
-- prop> forall n. (bea @m n * n) `mod` (natToNum @m) == 1
bea ∷
  ∀ m dom. (KnownNat m, HiddenClockResetEnable dom, 2 ≤ m) ⇒
  Channel dom (Mod m) →
  Channel dom (Mod m)
bea = enhance put get compute
 where
  put n
    | Rewrite ← using @(CLog2KeepsPositive m)
    = ( ( extend @_ @_ @(ModSize m - 1) $ unsignedToSigned $ bitCoerce n
        , m, 1, 0)
      , BeaStart
      )

  get _ ((_, _, _, y), _)
    | Rewrite ← using @(CLog2KeepsPositive m)
    = bitCoerce $ truncateB @_ @_ @(ModSize m - 1) $ signedToUnsigned y

  compute _ (s0@(u, v, x, y), mode0) = (, mode0 /= BeaEnd) $ case mode0 of
    BeaEnd                          → (s0,                   mode0    )
    BeaFin                          → (s0,                   BeaEnd   )
    BeaStart  | u == 1 || v == 1    → (finalize s0,          BeaFin   )
              | otherwise           → (s0,                   BeaMod2 0)
    BeaMod2 0 | lsb u == high       → (s0,                   BeaMod2 1)
              | otherwise           → (upd 0 $ upd 2 s0,     mode0    )
    BeaMod2 _ | lsb v == high       → (s0,                   BeaCmp   )
              | otherwise           → (upd 1 $ upd 3 s0,     mode0    )
    BeaCmp    | u >= v              → ((u - v, v, x - y, y), BeaMod 0 )
              | otherwise           → ((u, v - u, x, y - x), BeaMod 1 )
    BeaMod i  | val <= m && val < 0 → (set s0 i $ val + m,   mode0    )
              | val > m             → (set s0 i $ val - m,   mode0    )
              | i == 0              → (s0,                   BeaMod 2 )
              | i == 1              → (s0,                   BeaMod 3 )
              | otherwise           → (s0,                   BeaStart )
     where
      val = s0 !# i

  finalize (u, v, x, y) = (u, v, x, xy + if xy < 0 then m else 0)
   where
    xy = if u == 1 then x else y

  infixr !#
  (u, _, _, _) !# 0 = u ∷ BeaData m
  (_, v, _, _) !# 1 = v
  (_, _, x, _) !# 2 = x
  (_, _, _, y) !# _ = y

  set (_, v, x, y) 0 u = (u, v, x, y)
  set (u, _, x, y) 1 v = (u, v, x, y)
  set (u, v, _, y) 2 x = (u, v, x, y)
  set (u, v, x, _) _ y = (u, v, x, y)

  upd n c =
    set c n $ shiftR (c !# n + if lsb (c !# n) == low then 0 else m) 1

  m = natToNum @m

type BeaData m = Signed (ModSize m * 2)

data BeaMode
  = BeaStart | BeaMod2 (Index 2) | BeaCmp | BeaMod (Index 4) | BeaFin | BeaEnd
  deriving (Generic, NFDataX, Show, Eq)

-- * FastGCD

-- | Number of iterations for FastGCD based on the bitlength.
type Iterations (d ∷ Nat) =
  1 + If (d <=? 45) (Div (49 * d + 80 - 17) 17) (Div (49 * d + 57 - 17) 17)

type FastGCDIterations d = Iterations (ModSize d)

-- | Precomputed value used by FastGCD.
type Precomp (f ∷ Nat) =
  P.Mod (Div (f + 1) 2 ^ (FastGCDIterations f - 1)) f

type MulRegisterSize = 36
type GCDStreamingStages = 3

type DenMax m = FastGCDIterations m + 1

data FastGCDRecord len = FastGCD
 { remaining ∷ Index (len + 1)
 , delta     ∷ Signed (ModSize len + 1)
 , f         ∷ Signed (len + 1)
 , g         ∷ Signed (len + 1)
 , v         ∷ HWFraction (len + 1) len
 , r         ∷ HWFraction (len + 1) len
 } deriving (Generic, NFDataX)

type FastGCDState m = FastGCDRecord (FastGCDIterations m)

-- | A sequential implementation of the divSteps2 function described in
-- Bernstein/Yang's paper Fast constant-time gcd computation and modular
-- inversion.
divSteps ∷
  ∀ m dom.
  ( KnownNat m, HiddenClockResetEnable dom
  , KnownNat (FastGCDIterations m), 1 ≤ m, 1 ≤ FastGCDIterations m
  , ModSize m ≤ FastGCDIterations m
  ) ⇒
  Channel dom (Unsigned (ModSize m)) →
  Channel dom (Index (DenMax m), Signed (FastGCDIterations m + 1))
divSteps = enhance put get compute
 where
  put x = FastGCD
    { remaining = maxBound
    , delta = 1
    , f = natToNum @m
    , g = unsignedToSigned $ resize x
    , v = 0
    , r = 1
    } ∷ FastGCDState m

  get _ FastGCD{..}
    | HWFraction n x ← v
    = (maxBound - n - 1, if f < 0 then negate x else x)

  compute _ s@FastGCD{..}
    | remaining > 0 = Computing $ shifter $ shuffle s
    | otherwise     = Releasing s

  shuffle s@FastGCD{..} =
    if delta > 0 && bitToBool (lsb g)
    then s { delta = negate delta
           , f = g
           , g = negate f
           , v = r
           , r = negate v
           }
    else s ∷ FastGCDState m

  shifter s@FastGCD{..} = s
    { remaining = remaining - 1
    , delta = delta + 1
    , g = shiftR g1 1
    , r = shiftRFraction r1
    }
   where
    (g1, r1) =
      if bitToBool $ lsb g
      then (g + f, r + v)
      else (g, r)

-- | A sequential implementation for FastGCD. It shouldn't be used directly,
-- because better resource usage could be achieved by sharing subcomponents.
fastGcdSequential ∷
  ∀ m dom.
  ( KnownNat m, 1 ≤ m, HiddenClockResetEnable dom
  , 1 ≤ Iterations m, ModSize m ≤ FastGCDIterations m
  ) ⇒
  Channel dom (Mod m) →
  Channel dom (Mod m)
fastGcdSequential (divSteps @m . fmap bitCoerce → divResult)
  = computeModuloUnsigned @m
  $ karatsubaSequentialGated @GCDStreamingStages @MulRegisterSize
  $ fmap ((, natToNum @(Precomp m) ∷ Unsigned (ModSize m)) . bitCoerce)
  $ moduloShift @m
  $ zipRecent (flip (,) . fst) divResult
  $ computeModuloSigned @m
  $ snd <$> divResult

type FLTIterations m = ModSize (m - 2)

pattern FLTMul, FLTSquare ∷ Bool
pattern FLTSquare = False
pattern FLTMul = True

-- Add a step from the ECDSA document.
-- Has the restriction than the number must be < p^2.
-- TODO: Refactor this function somehow
splitNumber :: Unsigned 512 -> Signed 263
splitNumber a = t + s1 * 2 + s2 * 2 + s3 + s4 - d1 - d2 - d3 - d4
  where
    vA :: Vec 16 (Unsigned 32)
    vA = reverse $ bitCoerce a -- To have the right indices.
    fromIndices :: Vec n (Index 16) -> Vec n (Unsigned 32)
    fromIndices = map (vA !!)
    t,s1,s2,s3,s4,d1,d2,d3,d4 :: Signed 263
    t  = extend . unsignedToSigned . bitCoerce $
         fromIndices $(listToVecTH [7,6,5,4,3,2,1,0 :: Index 16])
    s1 = extend . unsignedToSigned . bitCoerce $
         fromIndices $(listToVecTH [15,14,13,12,11 :: Index 16]) ++ 0 :> 0 :> 0 :> Nil
    s2 = extend . unsignedToSigned . bitCoerce $
         0 :> fromIndices $(listToVecTH [15,14,13,12 :: Index 16]) ++ 0 :> 0 :> 0 :> Nil
    s3 = extend . unsignedToSigned . bitCoerce $
         fromIndices $(listToVecTH [15,14 :: Index 16]) ++ 0 :> 0 :> 0 :> Nil ++
         fromIndices $(listToVecTH [10,9,8 :: Index 16])
    s4 = extend . unsignedToSigned . bitCoerce $
        fromIndices $(listToVecTH [8,13,15,14,13,11,10,9 :: Index 16])
    d1 = extend . unsignedToSigned . bitCoerce $
         fromIndices $(listToVecTH [10,8 :: Index 16]) ++ 0 :> 0 :> 0 :> Nil ++
         fromIndices $(listToVecTH [13,12,11 :: Index 16])
    d2 = extend . unsignedToSigned . bitCoerce $
         fromIndices $(listToVecTH [11,9 :: Index 16]) ++ 0 :> 0 :> Nil ++
         fromIndices $(listToVecTH [15,14,13,12 :: Index 16])
    d3 = extend . unsignedToSigned . bitCoerce $ vA !! (12 :: Index 16) :> 0 :> Nil ++
         fromIndices $(listToVecTH [10,9,8,15,14,13 :: Index 16])
    d4 = extend . unsignedToSigned . bitCoerce $ vA !! (13 :: Index 16) :> 0 :> Nil ++
         fromIndices $(listToVecTH [11,10,9 :: Index 16]) ++
         0 :> fromIndices $(listToVecTH [15,14 :: Index 16])

splitNumberSeq :: forall dom. (HiddenClockResetEnable dom) =>
 Channel dom (Unsigned 512) -> Channel dom (Signed 263)
splitNumberSeq = enhance put get compute . fmap (reverse . bitCoerce)
 where
  put _ = (0, 0)
  
  compute :: Vec 16 (Unsigned 32) -> (Signed 263, Index 9) -> CompMode (Signed 263, Index 9)
  compute a (accum, 8) = Releasing (accum - selectIdx a 8, undefined)
  compute a (accum, 1) = Computing (accum + 2 * selectIdx a 1, 2)
  compute a (accum, 2) = Computing (accum + 2 * selectIdx a 2, 3)
  compute a (accum, i) = Computing (accum `op` selectIdx a i, satSucc SatBound i)
   where op = if i < 5 then (+) else (-)

  selectIdx :: Vec 16 (Unsigned 32) -> Index 9 -> Signed 263
  selectIdx a idx = extend . unsignedToSigned . bitCoerce $ map (maybe 0 (a !!)) (indices !! idx)

  get _ (accum, _) = accum
  
  indices :: Vec 9 (Vec 8 (Maybe (Index 16)))
  indices = t :> s1 :> s2 :> s3 :> s4 :> d1 :> d2 :> d3 :> d4 :> Nil
  
  t,s1,s2,s3,s4,d1,d2,d3,d4 :: Vec 8 (Maybe (Index 16))
  t  = $(listToVecTH $ L.map Just [7,6,5,4,3,2,1,0 :: Index 16])
  s1 = $(listToVecTH $ L.map Just [15,14,13,12,11 :: Index 16] <> L.replicate 3 Nothing)
  s2 = $(listToVecTH $ Nothing : (L.map Just [15,14,13,12 :: Index 16]) <> L.replicate 3 Nothing)
  s3 = $(listToVecTH $ L.map Just [15,14 :: Index 16] <> L.replicate 3 Nothing <> L.map Just [10,9,8])
  s4 = $(listToVecTH $ L.map Just [8,13,15,14,13,11,10,9 :: Index 16])
  d1 = $(listToVecTH $ L.map Just [10,8 :: Index 16] <> L.replicate 3 Nothing <> L.map Just [13,12,11])
  d2 = $(listToVecTH $ L.map Just [11,9 :: Index 16] <> L.replicate 2 Nothing <> L.map Just [15,14,13,12])
  d3 = $(listToVecTH $ [Just (12 :: Index 16), Nothing] <> L.map Just [10,9,8,15,14,13])
  d4 = $(listToVecTH $ [Just (13 :: Index 16), Nothing] <> L.map Just [11,10,9] <> [Nothing] <> L.map Just [15,14])

-- splitNumberSeq :: forall dom. (HiddenClockResetEnable dom) =>
--  Channel dom (Unsigned 512) -> Channel dom (Signed 263)
-- splitNumberSeq input = guardC done cur
--  where
--   indices :: Vec 9 (Vec 8 (Maybe (Index 16)))
--   indices = t :> s1 :> s2 :> s3 :> s4 :> d1 :> d2 :> d3 :> d4 :> Nil
  
--   t,s1,s2,s3,s4,d1,d2,d3,d4 :: Vec 8 (Maybe (Index 16))
--   t  = $(listToVecTH $ L.map Just [7,6,5,4,3,2,1,0 :: Index 16])
--   s1 = $(listToVecTH $ L.map Just [15,14,13,12,11 :: Index 16] <> L.replicate 3 Nothing)
--   s2 = $(listToVecTH $ Nothing : (L.map Just [15,14,13,12 :: Index 16]) <> L.replicate 3 Nothing)
--   s3 = $(listToVecTH $ L.map Just [15,14 :: Index 16] <> L.replicate 3 Nothing <> L.map Just [10,9,8])
--   s4 = $(listToVecTH $ L.map Just [8,13,15,14,13,11,10,9 :: Index 16])
--   d1 = $(listToVecTH $ L.map Just [10,8 :: Index 16] <> L.replicate 3 Nothing <> L.map Just [13,12,11])
--   d2 = $(listToVecTH $ L.map Just [11,9 :: Index 16] <> L.replicate 2 Nothing <> L.map Just [15,14,13,12])
--   d3 = $(listToVecTH $ [Just (12 :: Index 16), Nothing] <> L.map Just [10,9,8,15,14,13])
--   d4 = $(listToVecTH $ [Just (13 :: Index 16), Nothing] <> L.map Just [11,10,9] <> [Nothing] <> L.map Just [15,14])

--   reg :: Channel dom (Vec 16 (Unsigned 32))
--   reg = reverse . bitCoerce <$> input

--   cur :: Channel dom (Signed 263)
--   cur = keepD
--     -- $ fmap op
--     -- $ zipC idx
--     $ zipRecent op idx
--     $ zipC cur curVal

--   select _ Nothing  = 0
--   select v (Just i) = v !! i

--   curVal :: Channel dom (Signed 263)
--   curVal =
--     fmap (resize . bitCoerce)
--     $ fmap (\(r, i) -> map (select r) i)
--     $ zipC reg
--     $ fmap (indices !!) idx
  
--   idx :: Channel dom (Index 9)
--   idx = keepD
--     $ muxC input.hasUpdates (channel $ pure (0, Keep))
--     $ muxC cur.hasUpdates (fmap (satSucc SatBound) idx) idx

--   -- op :: (Index 9, (Signed 263, Signed 263)) -> Signed 263
--   op i (accum, v) = if i < 5 then accum + v else accum - v

--   done = content idx .== Just maxBound


-- | A working implementation of Inverse Modulo based on Fermat's Little
-- Theorem. Fine up to 256 bits, and only works with prime moduli.
fltCtmi ∷
  ∀ m dom. (KnownNat m,  HiddenClockResetEnable dom, 3 ≤ m, ModSize m ~ 256) ⇒
  Channel dom (Mod m) →
  Channel dom (Mod m)
fltCtmi (fmap bitCoerce → input) = bitCoerce <$> guardC done cur
 where
  cur = keepD
    $ join input
    $ fmap bitCoerce
    $ computeModuloSigned @m
    $ splitNumberSeq
    $ delayC
    $ karatsubaSequentialGated @GCDStreamingStages @MulRegisterSize
    $ zipC cur
    $ muxC (fst <$> stage) input
    $ guardC (not <$> done)
      cur

  stage = register (FLTSquare, minBound ∷ Index (FLTIterations m))
    $ apWhen input.hasUpdates (const (FLTSquare, maxBound))
    $ apWhen cur.hasUpdates nextStage
      stage
   where
    k = natToNum @(m - 2) ∷ BitVector (ModSize (m - 2))

    nextStage (m, i)
      | FLTSquare ← m, i > 0
      , testBit k $ fromEnum $ i - 1
      = (FLTMul, i)

      | otherwise
      = (FLTSquare, if i > 0 then i - 1 else i)

  done = stage .== (FLTSquare, minBound)

-- * SictMi

-- This algorithm comes from Jin and Miyaji's paper Short-Iteration
-- Constant-Time GCD and Modular inversion.

data SictMiState m = SictMi
 { remaining ∷ Index (SictIterations m + 1)
 , u         ∷ Signed (ModSize m + 1)
 , v         ∷ Signed (ModSize m + 1)
 , q         ∷ Signed (SictIterations m * 2 + 1)
 , r         ∷ Signed (SictIterations m * 2 + 1)
 } deriving (Generic, NFDataX, Show)

sictMiLoop ∷
  ∀ m dom. (KnownNat m, HiddenClockResetEnable dom, 1 ≤ m) ⇒
  Channel dom (Unsigned (ModSize m)) →
  Channel dom (Signed (SictIterations m * 2 + 1))
sictMiLoop = enhance put get compute
 where
  put input = SictMi
    { remaining = maxBound
    , u = unsignedToSigned input
    , v = natToNum @m
    , q = 0
    , r = 1
    }

  get _ SictMi{..} = q

  compute _ s@SictMi{..}
    | remaining > 0 = Computing $ next s
    | otherwise     = Releasing s

  next SictMi{..}
    | t2 >= t1  = SictMi (remaining - 1) t1 t2 t4 t3
    | otherwise = SictMi (remaining - 1) t2 t1 t3 t4
   where
    s  = bitToBool $ lsb u
    z  = bitToBool $ lsb v
    t1 = firstOp  s z v u
    t2 = secondOp s z v u `shiftR` 1
    t3 = firstOp  s z q r `shiftL` 1
    t4 = secondOp s z q r

    firstOp False False _ y = negate y
    firstOp True  True  _ y = y
    firstOp _     _     x y = x - y

    secondOp False False _ y = y `shiftL` 1
    secondOp False True  _ y = y
    secondOp True  False x _ = x
    secondOp True  True  x y = x - y

sictMiSequential ∷
  ∀ m dom.
  ( KnownNat m, HiddenClockResetEnable dom
  , 1 ≤ m, SictPrecompKnownNat m, 1 ≤ m - 2 * ModSize m
  , 2 * ModSize m ≤ m, 1 ≤ 2 * ModSize m * (m - 1)
  ) ⇒
  Channel dom (Mod m) →
  Channel dom (Mod m)
sictMiSequential
  = computeModuloUnsigned @m
  . karatsubaSequentialGated @GCDStreamingStages @MulRegisterSize
  . fmap ((, getSictPrecomp @m ∷ Unsigned (ModSize m)) . bitCoerce)
  . computeModuloSigned @m @(SictIterations m * 2)
  . sictMiLoop @m
  . fmap bitCoerce
