{-|
Module      : Clash.Crypto.Calculator.InverseModulo
Copyright   : Copyright © 2025-2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Various implementations of the inverse modulo operation over prime
fields.
-}

{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Clash.Crypto.Calculator.InverseModulo
  ( -- * BEA
    bea
    -- * FastGCD
  , Precomp
  , fastGcdSequential
    -- * FLT-CTMI
  , fltCtmi
  , fltCtmiE
    -- * SICT-MI
  , SictPrecomp
  , sictMiSequential
  ) where

import Clash.Prelude.Safe

import Clash.Class.NumConvert
import Clash.Signal.Channel

import Data.Constraint.Nat.Extra (CLog2KeepsPositive)
import Data.Type.Equality (type (==))
import GHC.TypeLits.KnownNat (KnownNat1(..), SNatKn(..), nameToSymbol)
import GHC.TypeNats.Proof (Rewrite(..), using, If)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Calculator.Fraction (Frac2(..), shiftRFrac2)
import Clash.Crypto.Calculator.Karatsuba
  (karatsubaSequential, karatsubaSequentialModulo)
import Clash.Crypto.Calculator.Modulo
  (ℤₘ, ModSize, moduloShift, computeModuloUnsigned, computeModuloSigned)

-- | A hardware implementation of the /Binary Euclidean Algorithm/.
-- It computes the inverse of a positive integer modulo m.
--
-- prop> ∀ n. (bea @m n * n) `mod` (natToNum @m) == 1
--
-- (Note that the algorithm currently will not terminate when providing
-- zero as the input.)
bea ∷
  ∀ m dom. (KnownNat m, HiddenClockResetEnable dom, 2 ≤ m) ⇒
  Channel dom (ℤₘ m) →
  Channel dom (ℤₘ m)
bea = enhance put get compute
 where
  put n
    | Rewrite ← using @(CLog2KeepsPositive m)
    , Rewrite ← Rewrite @(CLog 2 m ~ CLogWZ 2 m 0)
    = ( (numConvert $ bitCoerce @_ @(Unsigned _) n, m, 1, 0)
      , BeaStart
      )

  get _ ((_, _, _, y), _)
    | Rewrite ← using @(CLog2KeepsPositive m)
    = bitCoerce @(Unsigned (ModSize m))
    $ checkedTruncateB
    $ bitCoerce @(Signed (ModSize m + ModSize m))
    $ abs y

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

-- | Number of iterations for FastGCD based on the bitlength.
type Iterations (d ∷ Nat) =
  1 + If (d <=? 45) (Div (49 * d + 80 - 17) 17) (Div (49 * d + 57 - 17) 17)

type FastGCDIterations d = Iterations (ModSize d)

-- | The precomputed value used by FastGCD.
type Precomp (f ∷ Nat) =
  (((f + 1) `Div` 2) ^ (FastGCDIterations f - 1)) `Mod` f

type MulRegisterSize = 36
type GCDStreamingStages = 3

type DenMax m = FastGCDIterations m + 1

data FastGCDRecord len = FastGCD
 { remaining ∷ Index (len + 1)
 , delta     ∷ Signed (ModSize len + 1)
 , f         ∷ Signed (len + 1)
 , g         ∷ Signed (len + 1)
 , v         ∷ Frac2 (len + 1) len
 , r         ∷ Frac2 (len + 1) len
 } deriving (Generic, NFDataX)

type FastGCDState m = FastGCDRecord (FastGCDIterations m)

-- | A hardware implementation of the divSteps2 function described in
-- Bernstein/Yang's paper Fast constant-time gcd computation and modular
-- inversion.
divSteps ∷
  ∀ (dom ∷ Domain). HiddenClockResetEnable dom ⇒
  ∀ (m ∷ Nat) → (KnownNat m, 1 ≤ m) ⇒
  ( KnownNat (FastGCDIterations m)
  , 1 ≤ FastGCDIterations m
  , ModSize m ≤ FastGCDIterations m
  ) ⇒
  Channel dom (Unsigned (ModSize m)) →
  Channel dom (Index (DenMax m), Signed (FastGCDIterations m + 1))
divSteps m = enhance put get compute
 where
  put x = FastGCD
    { remaining = maxBound
    , delta = 1
    , f = natToNum @m
    , g = numConvert @(Unsigned (FastGCDIterations m)) $ resize x
    , v = 0
    , r = 1
    } ∷ FastGCDState m

  get _ FastGCD{..}
    | Frac2 n x ← v
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
    , r = shiftRFrac2 r1
    }
   where
    (g1, r1) =
      if bitToBool $ lsb g
      then (g + f, r + v)
      else (g, r)

-- | A hardware implementation of Bernstein's
-- [FastGCD](https://doi.org/10.13154/tches.v2019.i3.340-398)
-- algorithm. It should not be used directly, because better resource
-- usage can be achieved by sharing subcomponents.
fastGcdSequential ∷
  ∀ m dom.
  ( KnownNat m, 1 ≤ m, HiddenClockResetEnable dom
  , 1 ≤ Iterations m, ModSize m ≤ FastGCDIterations m
  ) ⇒
  Channel dom (ℤₘ m) →
  Channel dom (ℤₘ m)
fastGcdSequential (divSteps m . fmap bitCoerce → divResult)
  = computeModuloUnsigned @m
  $ karatsubaSequential GCDStreamingStages MulRegisterSize
  $ fmap ((, natToNum @(Precomp m) ∷ Unsigned (ModSize m)) . bitCoerce)
  $ moduloShift @m
  $ zipRecent (flip (,) . fst) divResult
  $ computeModuloSigned @m
  $ snd <$> divResult

pattern FLTMul, FLTSquare ∷ Bool
pattern FLTSquare = False
pattern FLTMul = True

-- | A hardware implementation of the
-- [FLT-CTMI](https://doi.org/10.1007/978-3-031-25319-5_5) algorithm
-- based on Fermat's Little Theorem. Fine up to 256 bits, and only
-- works with prime moduli.
fltCtmi ∷
  ∀ p dom. (KnownNat p, HiddenClockResetEnable dom, 3 ≤ p) ⇒
  Channel dom (ℤₘ p) →
  Channel dom (ℤₘ p)
fltCtmi (fmap bitCoerce → input) = fmap bitCoerce output
 where
  (output, s)
    = fltCtmiE (fmap (, p) input)
    $ karatsubaSequentialModulo GCDStreamingStages MulRegisterSize
    $ fmap (, p) s

  p = natToNum @(p - 1) + 1

-- | A 'fltCtmi' variant, which uses a shared multiplier and prime
-- field modulo instead of shipping a local copy.
fltCtmiE ∷
  ∀ n dom. (HiddenClockResetEnable dom, KnownNat n) ⇒
  -- | input
  Channel dom (Unsigned n, Unsigned n) →
  -- | shared multiplier with modulo output
  Channel dom (Unsigned n) →
  ( -- | output
    Channel dom (Unsigned n)
  , -- | shared multiplier with modulo input
    Channel dom (Unsigned n, Unsigned n)
  )
fltCtmiE (unzipC → (input, p)) smmOut =
  (guardC (done .&&. (delay False input.isNonEmpty)) cur, smmIn)
 where
  cur
    = keepD
    $ join input
    $ muxC (fst . snd <$> stage)
        (zipRecent const cur smmOut)
        smmOut

  smmIn
    = zipC cur
    $ muxC (fst <$> stage) input
    $ guardC (not <$> done) cur

  stage = register (FLTSquare, (False, minBound ∷ Index n))
    $ mux input.hasUpdates (pure (FLTSquare, (True, maxBound)))
    $ mux cur.hasUpdates
       (nextStage <$> (fmap (\x → x - 2) <$> p.content) <*> stage)
       stage
   where
    nextStage Nothing  _ = (FLTSquare, (False, minBound ∷ Index n))
    nextStage (Just k) (m, (skip, i))
      | skip && not (testBit k $ fromEnum i)
      = (FLTSquare, (True, i - 1))

      | FLTSquare ← m, i > 0
      , testBit k $ fromEnum $ i - 1
      = (FLTMul, (False, i))

      | otherwise
      = (FLTSquare, (False, if i > 0 then i - 1 else i))

  done = stage .== (FLTSquare, (False, minBound))

-- | The number of iterations of the main loop from the SICT-MI
-- algorithm.
type SictIterations m = 2 * ModSize m

-- | A type family for calculating the precomputed constant of the
-- SICT-MI algorithm.
type family SictPrecomp (m ∷ Nat) ∷ Nat where
  SictPrecomp 0 = 1
  SictPrecomp m = SictPrecomp# m (m - SictIterations m - 1) 2 1

-- | Helper of 'SictPrecomp'.
type family SictPrecomp# (m ∷ Nat) (pow ∷ Nat) (val ∷ Nat) (tmp ∷ Nat)  ∷ Nat where
  SictPrecomp# _ 0 _   _   = 1
  SictPrecomp# m 1 val tmp = (val * tmp) `Mod` m
  SictPrecomp# m n val tmp = SictPrecomp# m
                           -- even --          -- odd --
      (If (n `Mod` 2 == 0) (n `Div` 2)         (n - 1)            )
      (If (n `Mod` 2 == 0) (val * val `Mod` m) val                )
      (If (n `Mod` 2 == 0) (tmp `Mod` m)       (tmp * val `Mod` m))

instance (KnownNat m, 1 ≤ m) => KnownNat1 $(nameToSymbol ''SictPrecomp) m where
  natSing1 =
    let m = natToNum @m
        i = natToNum @(SictIterations m)
        calc 0 _   _   = 1
        calc 1 val tmp = val * tmp `mod` m
        calc n val tmp = calc
          (if n `mod` 2 == 0 then n `div` 2         else n - 1            )
          (if n `mod` 2 == 0 then val * val `mod` m else val              )
          (if n `mod` 2 == 0 then tmp `mod` m       else tmp * val `mod` m)
     in SNatKn $ calc (m - i - 1) 2 1
  {-# INLINE natSing1 #-}

data SictMiState m = SictMi
 { remaining ∷ Index (SictIterations m + 1)
 , u         ∷ Signed (ModSize m + 1)
 , v         ∷ Signed (ModSize m + 1)
 , q         ∷ Signed (SictIterations m * 2 + 1)
 , r         ∷ Signed (SictIterations m * 2 + 1)
 } deriving (Generic, NFDataX, Show)

sictMiLoop ∷
  ∀ (dom ∷ Domain). HiddenClockResetEnable dom ⇒
  ∀ (m ∷ Nat) → (KnownNat m, 1 ≤ m) ⇒
  Channel dom (Unsigned (ModSize m)) →
  Channel dom (Signed (SictIterations m * 2 + 1))
sictMiLoop m = enhance put get compute
 where
  put input = SictMi
    { remaining = maxBound
    , u = numConvert input
    , v = natToNum @m
    , q = 0
    , r = 1
    }

  get _ SictMi{..} = q

  compute _ (s@SictMi{..} ∷ SictMiState m)
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

-- | A hardware implementation of Jin and Miyaji's
-- [SICT-MI](https://doi.org/10.1007/978-3-031-25319-5_5) algorithm.
sictMiSequential ∷
  ∀ m dom.
  ( KnownNat m, HiddenClockResetEnable dom
  , 1 ≤ m - 2 * ModSize m, 1 ≤ SictPrecomp m
  , 2 * ModSize m ≤ m, 1 ≤ 2 * ModSize m * (m - 1)
  ) ⇒
  Channel dom (ℤₘ m) →
  Channel dom (ℤₘ m)
sictMiSequential
  = fmap bitCoerce
  . karatsubaSequentialModulo GCDStreamingStages MulRegisterSize
  . fmap ( (, natToNum @(m - 1) + 1)
         . (, natToNum @(SictPrecomp m) ∷ Unsigned (ModSize m))
         . bitCoerce
         )
  . computeModuloSigned @m @(SictIterations m * 2)
  . sictMiLoop m
  . fmap bitCoerce
