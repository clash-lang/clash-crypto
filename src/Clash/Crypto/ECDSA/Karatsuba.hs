{-# LANGUAGE MagicHash #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.ECDSA.Karatsuba where

import Clash.Prelude hiding ((++))
import Data.Constraint (Dict (..))
import Clash.Crypto.ECDSA.Lemmas
import Clash.Class.Counter (countSucc)
import qualified Clash.Signal.Delayed.Bundle as DB
import Unsafe.Coerce (unsafeCoerce)
import Data.Maybe (fromJust, isJust)
import Clash.Crypto.ECDSA.Utils (signedToUnsigned, groupMaybes3, groupMaybes)

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
  -- ^ the lower bound defining the base case at which standard
  -- multiplication is used instead of another recursive call
  Unsigned n -> Unsigned m -> Unsigned (n + m)
karatsuba regSize@SNat x y | Dict <- lemmaLowIsLess size =
  case compareSNat (SNat @(n + m)) regSize of
    SNatLE -> extend x * extend y
    SNatGT -> karatsuba' size
 where
  size = SNat :: SNat (Max n m)

  lemmaLowIsLess :: forall s. SNat s -> Dict (Low s <= s)
  lemmaLowIsLess _ = unsafeCoerce (Dict :: Dict (0 <= 0))

  karatsuba' :: forall s. Low s <= s => SNat s -> Unsigned (n + m)
  karatsuba' s@SNat = case compareSNat d4 s of
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
-- -- * Streaming implementations

-- TODO: Rewrite with counters instead of delays.
karatsubaStreamingSigned :: forall len streamingStages regSize dom.
  (KnownDomain dom, HiddenClockResetEnable dom, KnownNat len, KnownNat streamingStages,
  KnownNat regSize, len `Mod` (2 ^ (regSize + streamingStages)) ~ 0) =>
  Signal dom (Signed (len + 1)) ->
  Signal dom (Signed (len + 1)) ->
  Signal dom (Signed (len * 2 + 1))
karatsubaStreamingSigned s1 s2 =
 addSign <$> bundle (toSignal $ antiDelay @(3 ^ streamingStages) SNat sign, res)
 where
  addSign :: (Bit, Unsigned (len * 2)) -> Signed (len * 2 + 1)
  addSign (s, v) = (if s == low then id else negate) $ bitCoerce $ resize v
  res :: Signal dom (Unsigned (len * 2))
  res =
   karatsubaStreaming @len @streamingStages @regSize @(regSize + streamingStages)
   (fmap signedToUnsigned s1) (fmap signedToUnsigned s2)
  sign :: DSignal dom (3 ^ streamingStages) Bit
  sign = delayedI low $ fromSignal $ (\(a,b) -> msb a `xor` msb b) <$> bundle (s1, s2)

karatsubaStreamingSignedGated :: forall streamingStages regSize n m dom.
  (KnownDomain dom, HiddenClockResetEnable dom, KnownNat n, KnownNat m, KnownNat streamingStages,
  KnownNat regSize) =>
  Signal dom (Maybe (Signed (n + 1), Signed (m + 1))) ->
  Signal dom (Maybe (Signed (n + m + 1)))
karatsubaStreamingSignedGated mSignal =
 fmap addSign <$> (groupMaybes <$> sign <*> res)
 where
  addSign :: (Bit, Unsigned (n + m)) -> (Signed (n + m + 1))
  addSign (s,v) = (if s == low then id else negate) $ bitCoerce $ resize v
  res :: Signal dom (Maybe (Unsigned (n + m)))
  res =
   karatsubaStreamingGated @streamingStages @regSize @n @m $
   (fmap (\(a,b) -> (signedToUnsigned a, signedToUnsigned b)) <$> mSignal)
  sign :: Signal dom (Maybe Bit)
  sign = mux (isJust <$> mSignal) ((fmap (\(a,b) -> msb a `xor` msb b)) <$> mSignal) $ register Nothing sign

-- |A sequential implementation of the Karatsuba algorithm for multiplication.
-- It supports recursion on the size of its arguments, dividing the length
-- by 2 each time it recurs, relying on both sequential and combinatorial
-- subcircuits, which depths are configurable at type-level.
-- The circuit is usable each '3 ^ streamingStages' cycles, and is aligned
-- on '[1, 3 ^ streamingStages + 1, ...]'. Any values passed between these
-- two points in time will be discarded. All values produced between these
-- two points in time are unusable. 'regSize' gives the depth of the final
-- combinatorial circuit (the call to 'karatsuba#').
-- __Example:__
-- @
-- karatsuba_streaming @256 @2 @2 @4
-- @
-- will produce a sequential circuit with latency '9 = 3 ^ 2' that is able
-- to multiply two 256-bit unsigned numbers.
karatsubaStreaming :: forall len streamingStages regSize depth dom.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat regSize, KnownNat len,
  KnownNat depth, KnownNat streamingStages,
  len `Mod` (2 ^ (regSize + streamingStages)) ~ 0,
  regSize + streamingStages <= depth) =>
  Signal dom (Unsigned len) ->
  Signal dom (Unsigned len) ->
  Signal dom (Unsigned (len * 2))
karatsubaStreaming s1 s2 =
 truncateB <$> karatsubaStreaming# @len @streamingStages @regSize @depth
  (toUNat (SNat :: SNat streamingStages))
  (fmap extend s1) (fmap extend s2)

type KaratsubaCounter stages = (Index 3, Index (3 ^ (stages - 1)))

-- The `depth` type-level natural is needed for the carry. Without it, additions
-- can go awry. I chose to use 'depth' all throughout the circuit, but with
-- more clever type-level plays, it's possible to manage the depth
-- automatically.
karatsubaStreaming# :: forall len streamingStages regSize depth dom.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat regSize, KnownNat len,
  KnownNat streamingStages, KnownNat depth,
  len `Mod` (2 ^ (regSize + streamingStages)) ~ 0,
  regSize + streamingStages <= depth) =>
  UNat streamingStages ->
  Signal dom (Unsigned (len + depth)) ->
  Signal dom (Unsigned (len + depth)) ->
  Signal dom (Unsigned ((len + depth) * 2))
karatsubaStreaming# UZero s1 s2 = register 0 $
 uncurry (karatsuba @regSize SNat)
  <$> bundle (s1, s2)
karatsubaStreaming# (USucc streamingStagesLeft) x y
 | Dict <- lemma_pow @(streamingStages - 1)
 , Dict <- lemma_mod @len @(regSize + streamingStages)
 , Dict <- unsafeCoerce (Dict :: Dict (0 ~ 0)) :: Dict (len `Mod` 2 ~ 0)
 , _ :: UNat n <- streamingStagesLeft
 , Dict <- unsafeCoerce (Dict :: Dict (0 <= 0)) :: Dict (regSize + n <= depth)
 , Dict <- lemma_mul_div @len @2 =
 let
  xLow, yLow :: Signal dom (Unsigned (Div len 2 + depth))
  xHigh, yHigh :: Signal dom (Unsigned (Div len 2 + depth))
  xLow  = getLowPart @len <$> x
  yLow  = getLowPart @len <$> y
  xHigh = getHighPart @len <$> x
  yHigh = getHighPart @len <$> y
  counter :: Signal dom (KaratsubaCounter streamingStages)
  counter = register (0,0) $ fmap countSucc counter
  -- Register the new entries at the beginning of a cycle.
  muxCounter a b = mux ((== (0,0)) <$> counter) a $ register undefined b
  s1 = muxCounter (bundle (xHigh, yHigh)) s1
  s2 = muxCounter (bundle (xLow, yLow)) s2
  s3 = muxCounter (bundle (yHigh + yLow, xHigh + xLow)) s3
  spec :: Signal dom (Unsigned (Div len 2 + depth), Unsigned (Div len 2 + depth))
  spec = (\(a,b,c,(i,_)) -> head $ rotateLeft (a :> b :> c :> Nil) i) <$>
   bundle (s1,s2,s3,counter)
  output = uncurry (karatsubaStreaming# @_ @_ @regSize @depth streamingStagesLeft) $
   unbundle spec
  -- After one entire subcycle, we get the first result.
  result1 = mux ((== (1,0)) <$> counter) output $ register 0 result1
  result2 = mux ((== (2,0)) <$> counter) output $ register 0 result2
  finalResult = (\(z2, z0, z3) -> (z0, computeZ1 z3 z2 z0, z2)) <$>
    bundle (result1, result2, output)
 in
  (\(a, b, c) -> resize a +
  shiftL (resize b) (natToNum @(Div len 2)) +
  shiftL (resize c) (natToNum @len)) <$> finalResult

karatsubaStreamingGated :: forall streamingStages regSize n m dom.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat regSize, KnownNat n,
  KnownNat m, KnownNat streamingStages) =>
  (Signal dom (Maybe (Unsigned n, Unsigned m))) ->
  Signal dom (Maybe (Unsigned (n + m)))
karatsubaStreamingGated mSignal =
 fmap truncateB <$> karatsubaStreamingGated# @streamingStages @regSize @n @m SNat
  (toUNat (SNat :: SNat streamingStages)) (fmap (\(a,b) -> (resize a, resize b)) <$> mSignal)

lemmaLowIsLess :: forall s. Dict (Low s <= s)
lemmaLowIsLess = unsafeCoerce (Dict :: Dict (0 <= 0))

-- A variant that resets when it reads a Just value.
-- TODO: Only output once for each Just value.
karatsubaStreamingGated# :: forall streamingStages regSize n m dom s.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat regSize, KnownNat n,
  KnownNat streamingStages, KnownNat m, s ~ Max n m) =>
  SNat s ->
  UNat streamingStages ->
  Signal dom (Maybe (Unsigned n, Unsigned m)) ->
  Signal dom (Maybe (Unsigned (n + m)))
karatsubaStreamingGated# _ UZero s = register Nothing $
 fmap (uncurry (karatsuba @regSize SNat) <$>) s
karatsubaStreamingGated# SNat (USucc streamingStagesLeft) s
 | _ :: UNat streamLeft <- streamingStagesLeft
 , Dict <- lemma_pow @streamLeft
 , Dict <- lemmaLowIsLess @s
 , Dict <- (unsafeCoerce (Dict :: Dict (0 <= 0))) :: Dict (Low s <= High s)
 =
 let
  reset = isJust <$> s
  -- Restart the counter when we get a new Just-wrapped value.
  counter, pastCounter :: Signal dom (KaratsubaCounter streamingStages)
  counter = mux (reset .||. latched) (pure (0,0)) $ register (0,0) $ fmap countSucc counter
  pastCounter = register (0,0) counter
  -- Keep in mind last counter value so that we don't output trash values.
  outputCondition = ((== (maxBound, maxBound)) <$> pastCounter)
  -- x, y :: Signal dom (Unsigned (len + depth))
  x = mux reset ((fst . fromJust) <$> s) $ register 0 x
  y = mux reset ((snd . fromJust) <$> s) $ register 0 y
  xLow, yLow :: Signal dom (Unsigned (Low s))
  xHigh, yHigh :: Signal dom (Unsigned (High s))
  (xHigh, xLow) = unbundle $ fmap (bitCoerce . resize) x
  (yHigh, yLow) = unbundle $ fmap (bitCoerce . resize) y
  -- Register the new entries at the beginning of a cycle.
  muxCounter a b = mux reset a $ register undefined b
  s1, s2, s3 :: Signal dom (Unsigned (High s + 1), Unsigned (High s + 1))
  s1 = muxCounter (bundle (extend <$> xHigh, extend <$> yHigh)) s1
  s2 = muxCounter (bundle
    (extend <$> xLow,
     extend @_ @(Low s) @(High s - Low s + 1) <$> yLow)) s2
  s3 = muxCounter (bundle (fmap extend yHigh + fmap extend yLow,
                           fmap extend xHigh + fmap extend xLow)) s3
  spec :: Signal dom (Maybe (Unsigned (High s + 1), Unsigned (High s + 1)))
  spec = mux (((==0) . snd) <$> counter)
   ((\a b c (i,_) -> Just $ head $ rotateLeft (a :> b :> c :> Nil) i) <$>
                        s1 <*> s2 <*> s3 <*> counter)
   (pure Nothing)
  output, result1, result2 :: Signal dom (Maybe (Unsigned ((High s + 1) + (High s + 1))))
  output = karatsubaStreamingGated# @_ @regSize SNat streamingStagesLeft spec
  -- After one entire subcycle, we get the first result.
  result1 = mux ((== (1,0)) <$> counter) output $ register Nothing result1
  result2 = mux ((== (2,0)) <$> counter) output $ register Nothing result2
  finalResult =
   (fmap (\(z2, z0, z3) -> (z0, computeZ1 z3 z2 z0, z2))) <$>
   (groupMaybes3 <$> result1 <*> result2 <*> output)
  -- Latch the value only once.
  latched = mux reset
   (pure False) $
   mux (register True outputCondition .&&. register False (not <$> reset))
    (pure True) (register True latched)
  shiftLeft :: KnownNat a => Unsigned a -> SNat b -> Unsigned (a + b)
  shiftLeft a (SNat :: SNat b) = bitCoerce (a, 0 :: Unsigned b)
 in
  mux
   (outputCondition .&&. not <$> latched)
   ((fmap (\(a, b, c) ->
    resize a +
    resize (b `shiftLeft` (SNat :: SNat (Low s))) +
    resize (c `shiftLeft` (SNat :: SNat (Low s + Low s)))))
    <$> finalResult)
    -- undefined
   (pure Nothing)

-- * Delayed implementations.

-- |This implementation is the same as the one above (or at least it should)
-- but it uses 'DSignal' instead of 'Signal' for easier tracking.
karatsubaStreamingD :: forall len streamingStages regSize depth dom d.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat regSize, KnownNat len,
  KnownNat streamingStages, KnownNat depth,
  len `Mod` (2 ^ (regSize + streamingStages)) ~ 0,
  regSize + streamingStages <= depth) =>
  UNat streamingStages ->
  DSignal dom d (Unsigned (len + depth)) ->
  DSignal dom d (Unsigned (len + depth)) ->
  DSignal dom (d + 3 ^ streamingStages) (Unsigned ((len + depth) * 2))
karatsubaStreamingD UZero s1 s2 =
 delayedI 0 $
  uncurry (karatsuba @regSize SNat)
  <$> DB.bundle (s1, s2)
karatsubaStreamingD (USucc streamingStagesLeft) x y
 | Dict <- lemma_pow @(streamingStages - 1)
 , Dict <- lemma_mod @len @(regSize + streamingStages)
 , Dict <- unsafeCoerce (Dict :: Dict (0 ~ 0)) :: Dict (len `Mod` 2 ~ 0)
 , Dict <- lemma_mul_div @len @2 =
 let
  xLow, yLow :: DSignal dom d (Unsigned (Div len 2 + depth))
  xHigh, yHigh :: DSignal dom d (Unsigned (Div len 2 + depth))
  xLow  = getLowPart @len <$> x
  yLow  = getLowPart @len <$> y
  xHigh = getHighPart @len <$> x
  yHigh = getHighPart @len <$> y
  spec :: DSignal dom d (Unsigned (Div len 2 + depth), Unsigned (Div len 2 + depth))
  counter :: DSignal dom (d + 1) (KaratsubaCounter streamingStages)
  counter = delayedI (0,0) $ fmap countSucc counter
  s1 = DB.bundle (xHigh, yHigh)
  s2 = delayedI @(3 ^ (streamingStages - 1)) (0,0) $ fromSignal $
   bundle (xLow, yLow)
  s3 = delayedI @(2 * 3 ^ (streamingStages - 1)) (0,0) $ fromSignal $
   bundle (yHigh + yLow, xHigh + xLow)
  spec = (\(a,b,c,(i,_)) -> head $ rotateLeft (a :> b :> c :> Nil) i) <$>
   DB.bundle (s1,s2,s3,counter)
  o = uncurry (karatsubaStreamingD @_ @_ @regSize @depth streamingStagesLeft) $
   DB.unbundle spec
  result1 :: DSignal dom (2 * 3^(streamingStages - 1)) (Unsigned ((Div len 2 + depth) * 2))
  result1 = delayedI 0 o
  result2 :: DSignal dom (3 ^ streamingStages) (Unsigned ((Div len 2 + depth) * 2))
  result2 = delayedI 0 result1
  finalResult = (\(z2, z0, z3) -> (z0, computeZ1 z3 z2 z0, z2)) <$>
     DB.bundle (delayedI @(2 * 3 ^ (streamingStages - 1)) 0 o,
                delayedI @(3 ^ (streamingStages - 1)) 0 result1,
                result2)
 in
  (\(a, b, c) -> resize a +
  shiftL (resize b) (natToNum @(Div len 2)) +
  shiftL (resize c) (natToNum @len)) <$> finalResult

-- * Helper functions.

getLowPart :: forall len depth. (KnownNat len, KnownNat depth, len `Mod` 2 ~ 0) =>
  Unsigned (len + depth) -> Unsigned (len `Div` 2 + depth)
getLowPart
 | Dict <- lemma_mul_div @len @2 =
  extend . truncateB @_ @(Div len 2) @(Div len 2 + depth)

getHighPart :: forall len depth. (KnownNat len, KnownNat depth, len `Mod` 2 ~ 0) =>
  Unsigned (len + depth) -> Unsigned (len `Div` 2 + depth)
getHighPart = resize . (`shiftR` (natToNum @(Div len 2)))

computeZ1 :: forall len. KnownNat len =>
  Unsigned len -> Unsigned len -> Unsigned len -> Unsigned len
computeZ1 z3 z2 z0 = z3 - z2 - z0

