{-# LANGUAGE MagicHash #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.ECDSA.Karatsuba
 (karatsuba, karatsubaSequentialGated) --, karatsubaSequentialSignedGated)
where

import Clash.Prelude hiding ((++))
import Data.Constraint (Dict (..))
import Clash.Crypto.ECDSA.Lemmas
import Unsafe.Coerce (unsafeCoerce)
import Data.Maybe (isJust, fromMaybe)

-- * Combinatorial implementations

-- | The number of bits of the low part.
type Low  n = n `Div` 2

-- | The number of bits of the high part.
type High n = n - n `Div` 2

lemmaLowIsLess :: forall s. SNat s -> Dict (Low s <= s)
lemmaLowIsLess _ = unsafeCoerce (Dict :: Dict (0 <= 0))

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
karatsuba regSize@SNat x y | Dict <- lemmaLowIsLess size =
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
    extendRight :: forall b a. (KnownNat a, KnownNat b) => Unsigned a -> Unsigned (a + b)
    extendRight a = bitCoerce (a, 0 :: Unsigned b)

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
-- subcircuits, which depths are configurable at type-level. The circuit is
-- aligned on @ [1, 3 ^ streamingStages + 1, ...] @ (notwithstanding the resets).
-- 'regSize' gives the size of the registers, that will enable the algorithm to
-- compute the appropriate depth.
-- This algorithm uses three-step semantics and resets on `Just` values.
--
-- __Example:__
-- @
-- karatsubaSequentialGated @3 @36 @256 @256
-- @
-- will produce a sequential circuit with latency '9 = 3 ^ 2' that is able
-- to multiply two 256-bit unsigned numbers.
karatsubaSequentialGated :: forall streamingStages regSize n m dom.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat regSize, KnownNat n,
  KnownNat m, KnownNat streamingStages) =>
  Signal dom Bool ->
  Signal dom (Unsigned n, Unsigned m) ->
  Signal dom (Maybe (Unsigned (n + m)))
karatsubaSequentialGated toggle signal =
 fmap truncateB <$>
  karatsubaSequentialGated# @streamingStages @regSize @n @m
   (toUNat (SNat :: SNat streamingStages)) toggle
   signal

-- |The internal function called by `karatsubaSequentialGated`
karatsubaSequentialGated# :: forall streamingStages regSize n m dom s.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat regSize, KnownNat n,
  KnownNat streamingStages, KnownNat m, KnownNat s, s ~ Max n m) =>
  UNat streamingStages ->
  Signal dom Bool -> -- ^ Toggle line
  Signal dom (Unsigned n, Unsigned m) ->
  -- ^ Value line that has to be maintained during the entire computation
  Signal dom (Maybe (Unsigned (n + m)))
karatsubaSequentialGated# UZero toggle input = register Nothing $
 mux (toggle ./=. register False toggle)
 (Just . uncurry (karatsuba @regSize SNat) <$> input) (pure Nothing)
karatsubaSequentialGated# (USucc streamingStagesLeft) toggle input
 | _ :: UNat streamLeft <- streamingStagesLeft
 , Dict <- lemma_pow @streamLeft
 , Dict <- lemmaLowIsLess (SNat :: SNat s)
 , Dict <- unsafeCoerce (Dict :: Dict (0 <= 0)) :: Dict (Low s <= High s)
 =
 let
  toggleSwitched = toggle ./=. register False toggle
  -- 1. Separate the two numbers into a high part and a low part.
  x = fst <$> input
  y = snd <$> input
  xLow, yLow :: Signal dom (Unsigned (Low s))
  xHigh, yHigh :: Signal dom (Unsigned (High s))
  (xHigh, xLow) = unbundle $ bitCoerce . resize <$> x
  (yHigh, yLow) = unbundle $ bitCoerce . resize <$> y
  -- 2. Compute the values that'll be given to downstream multiplications.
  s1, s2, s3 :: Signal dom (Unsigned (High s + 1), Unsigned (High s + 1))
  s1 = bundle (extend <$> xHigh, extend <$> yHigh)
  s2 = bundle (extend <$> xLow,
                extend @_ @(Low s) @(High s - Low s + 1) <$> yLow)
  s3 = bundle (fmap extend yHigh + fmap extend yLow,
                fmap extend xHigh + fmap extend xLow)
  -- Collating these values into `inputVec` on which the algorithm will iterate.
  inputInit :: Signal dom (Vec 3 (Unsigned (High s + 1), Unsigned (High s + 1)))
  inputInit = liftA3 (\a b c -> a :> b :> c :> Nil) s1 s2 s3
  collatingVector :: Signal dom (Vec 3 (BitVector (2 * (High s + 1))))
  collatingVector = register def $
   mux toggleSwitched
   -- Reset the vector on toggling
    (bitCoerce <$> inputInit) $
    mux (isJust <$> output .&&. not <$> register False toggleSwitched .&&. not <$> latched)
     -- Insert the last output of Karatsuba in the vector when it's ready
     (liftA2 (<<+) collatingVector (bitCoerce . fromMaybe def <$> output))
     collatingVector
  -- 3. Collect the results from downstream multiplications into `results`.
  sendNew, childrenToggle :: Signal dom Bool
  sendNew = (isJust <$> register def output .||. register False toggleSwitched)
   .&&. not <$> latched .&&. (/=2) <$> outputCounter
  childrenToggle = register False $ mux sendNew (not <$> childrenToggle) childrenToggle
  inputVector :: Signal dom (Vec 3 (Unsigned (High s + 1), Unsigned (High s + 1)))
  inputVector = bitCoerce <$> collatingVector
  nextInput = at d0 <$> inputVector
  output :: Signal dom (Maybe (Unsigned ((High s + 1) * 2)))
  output = karatsubaSequentialGated# @_ @regSize streamingStagesLeft childrenToggle nextInput
  results :: Signal dom (Vec 3 (Unsigned ((High s + 1) * 2)))
  results = bitCoerce <$> collatingVector
  -- 4. When we get three total results, compute the final result.
  finalResult = register undefined
   (liftA3 (\z2 z0 z3 -> (z0, computeZ1 z3 z2 z0, z2))
   (at d0 <$> results) (at d1 <$> results) (at d2 <$> results))
  outputCounter :: Signal dom (Index 4)
  outputCounter = mux toggleSwitched 0 $ register 0 $
   mux (isJust <$> register Nothing output) (satAdd SatBound 1 <$> outputCounter) outputCounter
  outputCondition = (==3) <$> outputCounter
  -- Latch the value only once.
  latched =
   (not <$> toggleSwitched) .&&. outputCondition .&&. register False outputCondition
  extendRight :: forall b a. (KnownNat a, KnownNat b) =>
   Unsigned a -> Unsigned (a + b)
  extendRight a = bitCoerce (a, 0 :: Unsigned b)
 in
  mux
   (outputCondition .&&. not <$> latched)
   (Just <$> fmap (\(a, b, c) ->
    resize a +
    resize (extendRight @(Low s) b) +
    resize (extendRight @(Low s + Low s) c))
    finalResult)
   (pure Nothing)

-- -- |Same as `karatsubaSequentialGated`, but on signed integers.
-- karatsubaSequentialSignedGated :: forall streamingStages regSize n m dom.
--   (KnownDomain dom, HiddenClockResetEnable dom, KnownNat n, KnownNat m,
--   KnownNat streamingStages, KnownNat regSize) =>
--   Signal dom (Maybe (Signed (n + 1), Signed (m + 1))) ->
--   Signal dom (Maybe (Signed (n + m + 1)))
-- karatsubaSequentialSignedGated mSignal =
--  fmap addSign <$> (liftA2 (,) <$> sign <*> res)
--  where
--   addSign :: (Bit, Unsigned (n + m)) -> Signed (n + m + 1)
--   addSign (s,v) = (if s == low then id else negate) $ bitCoerce $ resize v
--   res :: Signal dom (Maybe (Unsigned (n + m)))
--   res =
--    karatsubaSequentialGated @streamingStages @regSize @n @m $
--    (fmap (bimap signedToUnsigned signedToUnsigned) <$> mSignal)
--   sign :: Signal dom (Maybe Bit)
--   sign =
--    mux (isJust <$> mSignal) (fmap (\(a,b) -> msb a `xor` msb b) <$> mSignal) $
--     register Nothing sign

-- * Helper functions.

computeZ1 :: forall len. KnownNat len =>
  Unsigned len -> Unsigned len -> Unsigned len -> Unsigned len
computeZ1 z3 z2 z0 = z3 - z2 - z0

