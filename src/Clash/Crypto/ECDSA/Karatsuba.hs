{-# LANGUAGE MagicHash #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.ECDSA.Karatsuba
 (karatsuba, karatsubaStreamingGated, karatsubaStreamingSignedGated)
where

import Clash.Prelude hiding ((++))
import Data.Constraint (Dict (..))
import Clash.Crypto.ECDSA.Lemmas
import Unsafe.Coerce (unsafeCoerce)
import Data.Maybe (isJust)
import Clash.Crypto.ECDSA.Utils (signedToUnsigned)
import Data.Bifunctor (Bifunctor(bimap))

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
  -- ^ the lower bound defining the base case at which standard
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
            + resize (z1 `shiftLeft` (SNat @(Low s)))
            + resize (z2 `shiftLeft` (SNat @(Low s + Low s)))
   where
    shiftLeft :: KnownNat a => Unsigned a -> SNat b -> Unsigned (a + b)
    shiftLeft a (SNat :: SNat b) = bitCoerce (a, 0 :: Unsigned b)

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
-- subcircuits, which depths are configurable at type-level. The circuit
-- is usable each '3 ^ streamingStages' cycles, and is aligned on '[1, 3 ^
-- streamingStages + 1, ...]'. 'regSize' gives the size of the registers, that
-- will enable the algorithm to compute the appropriate depth.
-- This algorithm uses three-step semantics and resets on `Just` values.
-- __Example:__
-- @
-- karatsubaSequentialGated @256 @2 @36
-- @
-- will produce a sequential circuit with latency '9 = 3 ^ 2' that is able
-- to multiply two 256-bit unsigned numbers.
karatsubaStreamingGated :: forall streamingStages regSize n m dom.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat regSize, KnownNat n,
  KnownNat m, KnownNat streamingStages) =>
  Signal dom (Maybe (Unsigned n, Unsigned m)) ->
  Signal dom (Maybe (Unsigned (n + m)))
karatsubaStreamingGated mSignal =
 fmap truncateB <$>
  karatsubaStreamingGated# @streamingStages @regSize @n @m SNat
   (toUNat (SNat :: SNat streamingStages))
   (fmap (bimap resize resize) <$> mSignal)

-- |The internal function called by `karatsubaStreamingGated`
karatsubaStreamingGated# :: forall streamingStages regSize n m dom s.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat regSize, KnownNat n,
  KnownNat streamingStages, KnownNat m, s ~ Max n m) =>
  SNat s ->
  UNat streamingStages ->
  Signal dom (Maybe (Unsigned n, Unsigned m)) ->
  Signal dom (Maybe (Unsigned (n + m)))
karatsubaStreamingGated# _ UZero s = register Nothing $
 fmap (uncurry (karatsuba @regSize SNat) <$>) s
karatsubaStreamingGated# stages@SNat (USucc streamingStagesLeft) s
 | _ :: UNat streamLeft <- streamingStagesLeft
 , Dict <- lemma_pow @streamLeft
 , Dict <- lemmaLowIsLess stages
 , Dict <- unsafeCoerce (Dict :: Dict (0 <= 0)) :: Dict (Low s <= High s)
 =
 let
  newInput = isJust <$> s
  x = (`maybe` fst) <$> register 0 x <*> s
  y = (`maybe` snd) <$> register 0 y <*> s
  xLow, yLow :: Signal dom (Unsigned (Low s))
  xHigh, yHigh :: Signal dom (Unsigned (High s))
  (xHigh, xLow) = unbundle $ bitCoerce . resize <$> x
  (yHigh, yLow) = unbundle $ bitCoerce . resize <$> y
  -- Register the new entries at the beginning of a cycle.
  muxCounter a b = mux newInput a $ register undefined b
  s1, s2, s3 :: Signal dom (Unsigned (High s + 1), Unsigned (High s + 1))
  s1 = muxCounter (bundle (extend <$> xHigh, extend <$> yHigh)) s1
  s2 = muxCounter (bundle
    (extend <$> xLow,
     extend @_ @(Low s) @(High s - Low s + 1) <$> yLow)) s2
  s3 = muxCounter (bundle (fmap extend yHigh + fmap extend yLow,
                           fmap extend xHigh + fmap extend xLow)) s3
  spec :: Signal dom (Maybe (Unsigned (High s + 1), Unsigned (High s + 1)))
  specInit = liftA3 (\a b c -> a :> b :> c :> Nil) s1 s2 s3
  specVec = mux newInput specInit $ register undefined $
   mux (isJust <$> output)
    ((\v -> rotateLeft v (1 :: Integer)) <$> specVec)
    specVec
  spec = mux (register False (isJust <$> output) .||. newInput)
   (Just . head <$> specVec)
   (pure Nothing)
  output :: Signal dom (Maybe (Unsigned ((High s + 1) + (High s + 1))))
  output = karatsubaStreamingGated# @_ @regSize SNat streamingStagesLeft spec
  results :: Signal dom (Vec 3 (Maybe (Unsigned ((High s + 1) + (High s + 1)))))
  rInit = Nothing :> Nothing :> Nothing :> Nil
  results = mux (latched .||. newInput) (pure rInit) $
   mux (isJust <$> output)
    (liftA2 (<<+) (register rInit results) output)
    (register rInit results)
  finalResult =
   liftA3 (\z2 z0 z3 -> (z0, computeZ1 z3 z2 z0, z2)) <$>
   ((!! (0 :: Integer)) <$> results) <*>
   ((!! (1 :: Integer)) <$> results) <*>
   ((!! (2 :: Integer)) <$> results)
  -- Latch the value only once.
  outputCondition = isJust . sequenceA <$> results
  latched = (not <$> newInput) .&&.
    (   (register True outputCondition .&&. register False (not <$> newInput))
    .||. register True latched
    )
  shiftLeft :: KnownNat a => Unsigned a -> SNat b -> Unsigned (a + b)
  shiftLeft a (SNat :: SNat b) = bitCoerce (a, 0 :: Unsigned b)
 in
  mux
   (outputCondition .&&. not <$> latched)
   (fmap (\(a, b, c) ->
    resize a +
    resize (b `shiftLeft` (SNat :: SNat (Low s))) +
    resize (c `shiftLeft` (SNat :: SNat (Low s + Low s))))
    <$> finalResult)
    -- undefined
   (pure Nothing)

-- |Same as `karatsubaStreamingGated`, but on signed integers.
karatsubaStreamingSignedGated :: forall streamingStages regSize n m dom.
  (KnownDomain dom, HiddenClockResetEnable dom, KnownNat n, KnownNat m,
  KnownNat streamingStages, KnownNat regSize) =>
  Signal dom (Maybe (Signed (n + 1), Signed (m + 1))) ->
  Signal dom (Maybe (Signed (n + m + 1)))
karatsubaStreamingSignedGated mSignal =
 fmap addSign <$> (liftA2 (,) <$> sign <*> res)
 where
  addSign :: (Bit, Unsigned (n + m)) -> Signed (n + m + 1)
  addSign (s,v) = (if s == low then id else negate) $ bitCoerce $ resize v
  res :: Signal dom (Maybe (Unsigned (n + m)))
  res =
   karatsubaStreamingGated @streamingStages @regSize @n @m $
   (fmap (bimap signedToUnsigned signedToUnsigned) <$> mSignal)
  sign :: Signal dom (Maybe Bit)
  sign =
   mux (isJust <$> mSignal) (fmap (\(a,b) -> msb a `xor` msb b) <$> mSignal) $
    register Nothing sign

-- * Helper functions.

computeZ1 :: forall len. KnownNat len =>
  Unsigned len -> Unsigned len -> Unsigned len -> Unsigned len
computeZ1 z3 z2 z0 = z3 - z2 - z0

