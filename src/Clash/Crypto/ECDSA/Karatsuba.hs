{-|
Module      : Clash.Crypto.ECDSA.Karatsuba
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Implementation of big-number multiplication using Karatsuba's
algorithm.
-}

{-# LANGUAGE MagicHash #-}

module Clash.Crypto.ECDSA.Karatsuba
  ( KaratsubaCycles
  , karatsuba
  , karatsubaSequentialGated
  ) where

import Clash.Prelude.Safe
import Clash.Signal.Channel
import Clash.Signal.Extra (apWhen)

import Data.Constraint.Nat.Extra (Div2RoundsDown, HalfIsLess)
import GHC.TypeNats.Proof (Rewrite(..), using)
import Language.Haskell.Unicode (type (≤))

-- * Combinatorial implementations

-- | The number of bits of the low part.
type Low  n = n `Div` 2

-- | The number of bits of the high part.
type High n = n - n `Div` 2

-- | Combinational Karatsuba implementation that recurses as long as
-- the size of at least one of the operands is larger than the given
-- lower bound @k@. Not meant to be synthesized in the case of large
-- numbers.
karatsuba ∷
  ∀ (n ∷ Nat) (m ∷ Nat). (KnownNat n, KnownNat m) ⇒
  -- | The lower bound defining the base case at which standard
  -- multiplication is used instead of another recursive call
  ∀ k → KnownNat k ⇒
  Unsigned n → Unsigned m → Unsigned (n + m)
karatsuba k x y | Rewrite ← using @(HalfIsLess (Max n m)) =
  case ( compareSNat (SNat @(n + m)) (SNat @k)
       , compareSNat (SNat @4) (SNat @(Max n m))
       ) of
    (SNatGT, SNatLE) → karatsuba# (Max n m)
    _                → extend x * extend y
 where
  karatsuba# ∷
    ∀ s → (KnownNat s, 4 ≤ s, Low s ≤ s) ⇒
    Unsigned (n + m)
  karatsuba# s = case compareSNat (SNat @4) (SNat @s) of
    SNatGT → extend x * extend y
    SNatLE → resize z0
           + resize (extendRight @(Low s) z1)
           + resize (extendRight @(Low s + Low s) z2)
   where
    xLow,  yLow  ∷ Unsigned (Low s)
    xHigh, yHigh ∷ Unsigned (High s)
    (xHigh, xLow) = bitCoerce $ resize x
    (yHigh, yLow) = bitCoerce $ resize y

    xSum, ySum ∷ Unsigned (High s + 1)
    xSum = resize xHigh + resize xLow
    ySum = resize yHigh + resize yLow

    z0, z1, z2 ∷ Unsigned ((High s + 1) + (High s + 1))
    z0 = resize $ karatsuba k xLow yLow
    z2 = resize $ karatsuba k xHigh yHigh
    z3 = karatsuba k xSum ySum
    z1 = z3 - z2 - z0

-- -- * Sequential implementations

-- |The number of cycles an instance of 'karatsubaSequentialGated` takes to run.
type KaratsubaCycles stages = 2 * (3 ^ stages - 1)

-- |A sequential implementation of the Karatsuba algorithm for multiplication.
-- It supports recursion on the size of its arguments, dividing the length
-- by 2 each time it recurs, relying on both sequential and combinatorial
-- subcircuits, which depths are configurable at type-level.  'regSize' gives
-- the size of the multiplication units of the board, that will enable the
-- algorithm to compute the appropriate depth.
-- This algorithm uses two-step semantics with a toggle line that starts on
-- `False`.
--
-- __Example:__
-- @
-- karatsubaSequentialGated @3 @36 @256 @256
-- @
-- will produce a sequential circuit with latency '52 = 2 * (3 ^ cycles - 1)'
-- that is able to multiply two 256-bit unsigned numbers.
karatsubaSequentialGated ∷
  ∀ (n ∷ Nat) (m ∷ Nat) (dom ∷ Domain).
  ( KnownNat n, KnownNat m, HiddenClockResetEnable dom) ⇒
  ∀ stages → KnownNat stages ⇒
  ∀ k → KnownNat k ⇒
  Channel dom (Unsigned n, Unsigned m) →
  Channel dom (Unsigned (n + m))
karatsubaSequentialGated stages k
  | Rewrite ← using @(HalfIsLess (Max n m))
  = karatsubaSequentialGated# (Max n m)
  $ toUNat (SNat @stages)
 where
  {-# NOINLINE karatsubaSequentialGated# #-}
  karatsubaSequentialGated# ∷
    ∀ s → (KnownNat s, s ~ Max n m, HalfIsLess s, Div2RoundsDown s) ⇒
    UNat stages →
    Channel dom (Unsigned n, Unsigned m) →
    Channel dom (Unsigned (n + m))

  -- run combinational karatsuba and release the result
  karatsubaSequentialGated# _ UZero input
    = uncurry (karatsuba k) <$> input

  karatsubaSequentialGated# s (USucc _) input
    = fromVec <$> guardC done cur
   where
    -- Collating these values into a vector on which the algorithm will iterate.
    cur = keepD @(Vec 3 (BitVector (2 * (High s + 1)))) next

    next
      = join (toVec <$> input)
      $ zipRecent (<<+) cur
      $ fmap pack
      $ karatsubaSequentialGated (type (stages - 1)) k
      $ guardC (not <$> done)
      $ fmap (bitCoerce @_ @(Unsigned (High s + 1), Unsigned (High s + 1)) . head)
        cur

    done = iteration .== 0
     where
      iteration = register (minBound ∷ Index 4)
        $ apWhen input.hasUpdates (const maxBound)
        $ apWhen next.hasUpdates (satPred SatBound)
          iteration

    -- Separate the two numbers into a high part and a low part and
    -- compute the values that'll be given to downstream
    -- multiplications.
    toVec (a, b) = bitCoerce
      $  extend xHigh
      :> extend yHigh
      :> extend xLow
      :> extend @_ @_ @(High s - Low s + 1) yLow
      :> extend yHigh + extend yLow
      :> extend xHigh + extend xLow
      :> Nil
     where
      xLow, yLow   ∷ Unsigned (Low s)
      xHigh, yHigh ∷ Unsigned (High s)
      (xHigh, xLow) = bitCoerce $ resize a
      (yHigh, yLow) = bitCoerce $ resize b

    fromVec (bitCoerce → (z2, z0, z3))
      = resize (z0 ∷ Unsigned ((High s + 1) * 2))
      + resize (extendRight @(Low s) (computeZ1 z3 z2 z0))
      + resize (extendRight @(Low s + Low s) z2)

-- * Helper functions.

computeZ1 ∷
  ∀ len. KnownNat len ⇒
  Unsigned len → Unsigned len → Unsigned len → Unsigned len
computeZ1 z3 z2 z0 = z3 - z2 - z0

extendRight ∷
  ∀ b a. (KnownNat a, KnownNat b) ⇒
  Unsigned a → Unsigned (a + b)
extendRight a = bitCoerce (a, 0 ∷ Unsigned b)
