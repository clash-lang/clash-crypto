{-# LANGUAGE MagicHash #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.ECDSA.Karatsuba where

import Clash.Prelude hiding ((++))
import Data.Constraint (Dict (..))
import Clash.Crypto.ECDSA.Lemmas
import Clash.Class.Counter (countSucc)
import qualified Clash.Signal.Delayed.Bundle as DB
import Unsafe.Coerce (unsafeCoerce)

-- * Combinatorial implementations

-- TODO: Extend the split to any size. Not super useful though, unless it's for
-- genericity.
-- TODO: Make the 'depth' parameter automatically inferred through generation.

-- |A combinatorial implementation of the Karatsuba algorithm for multiplication.
-- It's not intended to be used as-is, because it gives rise to a circuit too big
-- to be synthesized and/or fast.
-- However, it supports recursion on the size of its arguments, dividing the length
-- by 2 each time it recurs.
karatsuba :: forall stages len depth.
 (KnownNat depth, KnownNat len, KnownNat stages,
  len `Mod` (2 ^ stages) ~ 0, stages <= depth) =>
  Unsigned (len + depth) -> -- ^ x
  Unsigned (len + depth) -> -- ^ y
  Unsigned ((len + depth) * 2) -- ^ x * y
karatsuba = karatsuba# @len @stages @depth (toUNat SNat)

karatsuba# :: forall len stages depth.
 (KnownNat len, KnownNat stages, KnownNat depth,
  len `Mod` (2 ^ stages) ~ 0, stages <= depth) =>
  UNat stages ->
  Unsigned (len + depth) ->
  Unsigned (len + depth) ->
  Unsigned ((len + depth) * 2)
karatsuba# UZero x y = resize x * resize y
karatsuba# (USucc stagesLeft) x y
 | Dict <- lemma_mod @len @stages
 , Dict <- unsafeCoerce (Dict :: Dict (0 ~ 0)) :: Dict (len `Mod` 2 ~ 0)
 , _ :: UNat n <- stagesLeft
 , Dict <- unsafeCoerce (Dict :: Dict (0 <= 0)) :: Dict (n <= depth)
 , Dict <- lemma_mul_div @len @2 =
 let
  -- All the subsequent carry bits will be in the high parts, and that's why we
  -- have to truncate the low parts, and shift only by '@(Div len 2)'.
  xLow, yLow :: Unsigned (Div len 2 + depth)
  xHigh, yHigh :: Unsigned (Div len 2 + depth)
  xLow  = getLowPart @len x
  yLow  = getLowPart @len y
  xHigh = getHighPart @len x
  yHigh = getHighPart @len y
  z0, z1, z2, z3 :: Unsigned (len + depth * 2)
  z2 = karatsuba# @(Div len 2) stagesLeft xHigh yHigh
  z0 = karatsuba# @(Div len 2) stagesLeft xLow yLow
  z3 = karatsuba# @(Div len 2) stagesLeft (xHigh + xLow) (yHigh + yLow)
  z1 = computeZ1 z3 z2 z0
 in
  resize z0 +
  shiftL (resize z1) (natToNum @(Div len 2)) +
  shiftL (resize z2) (natToNum @len)

-- -- * Streaming implementations

karatsubaStreamingSigned :: forall len streamingStages combStages dom.
  (KnownDomain dom, HiddenClockResetEnable dom, KnownNat len, KnownNat streamingStages,
  KnownNat combStages, len `Mod` (2 ^ (combStages + streamingStages)) ~ 0) =>
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
   karatsubaStreaming @len @streamingStages @combStages @(combStages + streamingStages)
   (fmap signedToUnsigned s1) (fmap signedToUnsigned s2)
  sign :: DSignal dom (3 ^ streamingStages) Bit
  sign = delayedI low $ fromSignal $ (\(a,b) -> msb a `xor` msb b) <$> bundle (s1, s2)

-- |A sequential implementation of the Karatsuba algorithm for multiplication.
-- It supports recursion on the size of its arguments, dividing the length
-- by 2 each time it recurs, relying on both sequential and combinatorial
-- subcircuits, which depths are configurable at type-level.
-- The circuit is usable each '3 ^ streamingStages' cycles, and is aligned
-- on '[1, 3 ^ streamingStages + 1, ...]'. Any values passed between these
-- two points in time will be discarded. All values produced between these
-- two points in time are unusable. 'combStages' gives the depth of the final
-- combinatorial circuit (the call to 'karatsuba#').
-- __Example:__
-- @
-- karatsuba_streaming @256 @2 @2 @4
-- @
-- will produce a sequential circuit with latency '9 = 3 ^ 2' that is able
-- to multiply two 256-bit unsigned numbers.
karatsubaStreaming :: forall len streamingStages combStages depth dom.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat combStages, KnownNat len,
  KnownNat depth, KnownNat streamingStages,
  len `Mod` (2 ^ (combStages + streamingStages)) ~ 0,
  combStages + streamingStages <= depth) =>
  Signal dom (Unsigned len) ->
  Signal dom (Unsigned len) ->
  Signal dom (Unsigned (len * 2))
karatsubaStreaming s1 s2 =
 truncateB <$> karatsubaStreaming# @len @streamingStages @combStages @depth
  (toUNat (SNat :: SNat streamingStages))
  (fmap extend s1) (fmap extend s2)

type KaratsubaCounter stages = (Index 3, Index (3 ^ (stages - 1)))

-- The `depth` type-level natural is needed for the carry. Without it, additions
-- can go awry. I chose to use 'depth' all throughout the circuit, but with
-- more clever type-level plays, it's possible to manage the depth
-- automatically.
karatsubaStreaming# :: forall len streamingStages combStages depth dom.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat combStages, KnownNat len,
  KnownNat streamingStages, KnownNat depth,
  len `Mod` (2 ^ (combStages + streamingStages)) ~ 0,
  combStages + streamingStages <= depth) =>
  UNat streamingStages ->
  Signal dom (Unsigned (len + depth)) ->
  Signal dom (Unsigned (len + depth)) ->
  Signal dom (Unsigned ((len + depth) * 2))
karatsubaStreaming# UZero s1 s2 = register 0 $
 uncurry (karatsuba# @len @combStages @depth (toUNat (SNat :: SNat combStages)))
  <$> bundle (s1, s2)
karatsubaStreaming# (USucc streamingStagesLeft) x y
 | Dict <- lemma_pow @(streamingStages - 1)
 , Dict <- lemma_mod @len @(combStages + streamingStages)
 , Dict <- unsafeCoerce (Dict :: Dict (0 ~ 0)) :: Dict (len `Mod` 2 ~ 0)
 , _ :: UNat n <- streamingStagesLeft
 , Dict <- unsafeCoerce (Dict :: Dict (0 <= 0)) :: Dict (combStages + n <= depth)
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
  muxCounter a b = register (0,0) $ mux ((== (0,0)) <$> counter) a b
  s1 = muxCounter (bundle (xHigh, yHigh)) s1
  s2 = muxCounter (bundle (xLow, yLow)) s2
  s3 = muxCounter (bundle (yHigh + yLow, xHigh + xLow)) s3
  spec :: Signal dom (Unsigned (Div len 2 + depth), Unsigned (Div len 2 + depth))
  spec = (\(a,b,c,(i,_)) -> head $ rotateLeft (a :> b :> c :> Nil) i) <$>
   bundle (s1,s2,s3,counter)
  output = uncurry (karatsubaStreaming# @_ @_ @combStages @depth streamingStagesLeft) $
   unbundle spec
  -- After one entire subcycle, we get the first result.
  result1 = register 0 $ mux ((== (1,0)) <$> counter) output result1
  result2 = register 0 $ mux ((== (2,0)) <$> counter) output result2
  finalResult = (\(z2, z0, z3) -> (z0, computeZ1 z3 z2 z0, z2)) <$>
    bundle (result1, result2, output)
 in
  (\(a, b, c) -> resize a +
  shiftL (resize b) (natToNum @(Div len 2)) +
  shiftL (resize c) (natToNum @len)) <$> finalResult

-- * Delayed implementations.

-- |This implementation is the same as the one above (or at least it should)
-- but it uses 'DSignal' instead of 'Signal' for easier tracking.
karatsubaStreamingD :: forall len streamingStages combStages depth dom d.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat combStages, KnownNat len,
  KnownNat streamingStages, KnownNat depth,
  len `Mod` (2 ^ (combStages + streamingStages)) ~ 0,
  combStages + streamingStages <= depth) =>
  UNat streamingStages ->
  DSignal dom d (Unsigned (len + depth)) ->
  DSignal dom d (Unsigned (len + depth)) ->
  DSignal dom (d + 3 ^ streamingStages) (Unsigned ((len + depth) * 2))
karatsubaStreamingD UZero s1 s2 =
 delayedI 0 $
  uncurry (karatsuba# @len @combStages @depth (toUNat (SNat :: SNat combStages)))
  <$> DB.bundle (s1, s2)
karatsubaStreamingD (USucc streamingStagesLeft) x y
 | Dict <- lemma_pow @(streamingStages - 1)
 , Dict <- lemma_mod @len @(combStages + streamingStages)
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
  o = uncurry (karatsubaStreamingD @_ @_ @combStages @depth streamingStagesLeft) $
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

unsignedToSigned :: forall len . KnownNat len => Unsigned len -> Signed (len + 1)
unsignedToSigned = bitCoerce . zeroExtend

signedToUnsigned :: forall len . KnownNat len => Signed (len + 1) -> Unsigned len
signedToUnsigned = bitCoerce . truncateB . abs


