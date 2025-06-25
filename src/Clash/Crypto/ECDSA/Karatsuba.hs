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
{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.ECDSA.Karatsuba
 (karatsuba, karatsubaSequentialGated)
where

import Clash.Crypto.ECDSA.Lemmas
import Clash.Prelude hiding ((++))
import Clash.Netlist.Util (orNothing)
import Data.Constraint (Dict (..))
import Data.Functor ((<&>))
import Data.Maybe (isJust)
import Unsafe.Coerce (unsafeCoerce)
import GHC.TypeNats.Proof

-- * Combinatorial implementations

-- | The number of bits of the low part.
type Low  n = n `Div` 2

-- | The number of bits of the high part.
type High n = n - n `Div` 2

-- | Combinational Karatsuba implementation that recurses as long as
-- the size of at least one of the operands is larger than the given
-- lower bound @k@. Not meant to be synthesized in the case of large
-- numbers.
karatsuba ::
  forall regSize n m. (KnownNat n, KnownNat m) =>
  SNat regSize ->
  -- ^ The lower bound defining the base case at which standard
  -- multiplication is used instead of another recursive call
  Unsigned n -> Unsigned m -> Unsigned (n + m)
karatsuba regSize@SNat x y | Dict <- lemmaLowIsLess @(Max n m) =
  case compareSNat (SNat @(n + m)) regSize of
    SNatLE -> extend x * extend y
    SNatGT -> karatsubaInternal size
 where
  size = SNat :: SNat (Max n m)

  karatsubaInternal :: forall s. Low s <= s => SNat s -> Unsigned (n + m)
  karatsubaInternal s@SNat = case compareSNat d4 s of
    SNatGT -> extend x * extend y
    SNatLE -> resize z0
            + resize (extendRight @(Low s) z1)
            + resize (extendRight @(Low s + Low s) z2)
   where
    xLow,  yLow  :: Unsigned (Low s)
    xHigh, yHigh :: Unsigned (High s)
    (xHigh, xLow) = bitCoerce $ resize x
    (yHigh, yLow) = bitCoerce $ resize y

    xSum, ySum :: Unsigned (High s + 1)
    xSum = resize xHigh + resize xLow
    ySum = resize yHigh + resize yLow

    z0, z1, z2 :: Unsigned ((High s + 1) + (High s + 1))
    z0 = resize $ karatsuba regSize xLow yLow
    z2 = resize $ karatsuba regSize xHigh yHigh
    z3 = karatsuba regSize xSum ySum
    z1 = z3 - z2 - z0

-- -- * Sequential implementations

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
-- will produce a sequential circuit with latency '9 = 3 ^ 2' that is able
-- to multiply two 256-bit unsigned numbers.
karatsubaSequentialGated :: forall streamingStages regSize n m dom s.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat regSize, KnownNat n,
  KnownNat streamingStages, KnownNat m, KnownNat s, s ~ Max n m) =>
  Signal dom Bool -> -- ^ Toggle line
  Signal dom (Unsigned n) ->
  Signal dom (Unsigned m) ->
  -- ^ Value line that has to be maintained during the entire computation
  Signal dom (Maybe (Unsigned (n + m)))
karatsubaSequentialGated =
 karatsubaSequentialGated# @streamingStages @regSize @n @m @dom @s
  (toUNat (SNat :: SNat streamingStages))

-- |The internal function called by `karatsubaSequentialGated`.
karatsubaSequentialGated# :: forall streamingStages regSize n m dom s.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat regSize, KnownNat n,
  KnownNat streamingStages, KnownNat m, KnownNat s, s ~ Max n m) =>
  UNat streamingStages ->
  Signal dom Bool -> -- ^ Toggle line
  Signal dom (Unsigned n) ->
  Signal dom (Unsigned m) ->
  -- ^ Value line that has to be maintained during the entire computation
  Signal dom (Maybe (Unsigned (n + m)))
karatsubaSequentialGated# UZero toggle x y = register Nothing $
 mux (toggle ./=. register False toggle)
 (Just <$> liftA2 (karatsuba @regSize SNat) x y) (pure Nothing)
karatsubaSequentialGated# (USucc streamingStagesLeft) toggle x y
 | _ :: UNat streamLeft <- streamingStagesLeft
 , Rewrite <- using @(LemmaPow streamLeft)
 , Dict <- lemmaLowIsLess @s
 , Dict <- lemmaLowIsLessThanHigh @s
 =
 let
  toggleSwitched = toggle ./=. register False toggle
  -- 1. Separate the two numbers into a high part and a low part.
  --    and compute the values that'll be given to downstream multiplications.
  restructure a b =
   let
    xLow, yLow   :: Unsigned (Low s)
    xHigh, yHigh :: Unsigned (High s)
    (xHigh, xLow) = bitCoerce $ resize a
    (yHigh, yLow) = bitCoerce $ resize b
   in
    bitCoerce
     $  extend xHigh
     :> extend yHigh
     :> extend xLow
     :> extend @_ @_ @(High s - Low s + 1) yLow
     :> extend yHigh + extend yLow
     :> extend xHigh + extend xLow
     :> Nil
  -- Collating these values into `inputVec` on which the algorithm will iterate.
  collatingVector :: Signal dom (Vec 3 (BitVector (2 * (High s + 1))))
  collatingVector = register def
   -- Reset the vector on toggling
   $ mux toggleSwitched (liftA2 restructure x y)
    -- Don't update if already latched or if a new input just arrived
    $ mux (register False toggleSwitched .||. latched) collatingVector
     -- Insert the last output of Karatsuba in the vector when it's ready
     $ (\c -> maybe c ((c <<+) . bitCoerce)) <$> collatingVector <*> output
  -- 2. Collect the results from downstream multiplications.
  sendNew, childrenToggle :: Signal dom Bool
  sendNew = register False (isJust <$> output .||. toggleSwitched) .&&.
            not <$> latched .&&. (/=2) <$> outputCounter
  childrenToggle = register False $ childrenToggle ./=. sendNew
  inputVector :: Signal dom (Vec 3 (Unsigned (High s + 1), Unsigned (High s + 1)))
  inputVector = bitCoerce <$> collatingVector
  output :: Signal dom (Maybe (Unsigned ((High s + 1) * 2)))
  (nextX, nextY) = unbundle $ head <$> inputVector
  output = karatsubaSequentialGated# @_ @regSize streamingStagesLeft
   childrenToggle nextX nextY
  -- 3. When we get three total results, compute the final result.
  finalResult = register undefined $
    fmap bitCoerce collatingVector <&> \(z2, z0, z3) ->
      (z0 :: Unsigned ((High s + 1) * 2), computeZ1 z3 z2 z0, z2)
  outputCounter :: Signal dom (Index 4)
  outputCounter = mux toggleSwitched 0 $ register 0 $
   mux (register False (isJust <$> output))
    (satAdd SatBound 1 <$> outputCounter)
    outputCounter
  outputCondition = (==3) <$> outputCounter
  -- Latch the value only once.
  latched =
   (not <$> toggleSwitched) .&&.
   outputCondition .&&.
   register False outputCondition
 in
   orNothing
    <$> (outputCondition .&&. not <$> latched)
    <*> (finalResult <&> \(a, b, c) ->
           resize a +
           resize (extendRight @(Low s) b) +
           resize (extendRight @(Low s + Low s) c)
        )

-- * Helper functions.

computeZ1 :: forall len. KnownNat len =>
  Unsigned len -> Unsigned len -> Unsigned len -> Unsigned len
computeZ1 z3 z2 z0 = z3 - z2 - z0

extendRight :: forall b a. (KnownNat a, KnownNat b) =>
 Unsigned a -> Unsigned (a + b)
extendRight a = bitCoerce (a, 0 :: Unsigned b)

-- * Lemmas

lemmaLowIsLess :: forall s. Dict (Low s <= s)
lemmaLowIsLess = unsafeCoerce (Dict :: Dict (0 <= 0))

lemmaLowIsLessThanHigh :: forall s. Dict (Low s <= High s)
lemmaLowIsLessThanHigh = unsafeCoerce (Dict :: Dict (0 <= 0))

