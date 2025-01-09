{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.ECDSA.Karatsuba where

import Clash.Prelude hiding ((++))
import qualified GHC.TypeNats as P
import Data.Constraint (Dict (..))
import Clash.Crypto.ECDSA.Lemmas
import Clash.Crypto.ECDSA.Utils (signedToUnsigned)
import Clash.Class.Counter (countSucc)
import qualified Clash.Signal.Delayed.Bundle as DB

-- * Combinatorial implementations

-- TODO: Extend the split to any size. Not super useful though, unless it's for
-- genericity.
-- TODO: Make the `depth` parameter automatically inferred through generation.

-- |A combinatorial implementation of the Karatsuba algorithm for multiplication.
-- It's not intended to be used as-is, because it gives rise to a circuit too big
-- to be synthesized and/or fast.
-- However, it supports recursion on the size of its arguments, dividing the length
-- by 2 each time it recurs.
karatsuba :: forall stages len depth. (KnownNat depth, KnownNat len, KnownNat stages, P.Mod len (2 ^ stages) ~ 0, stages <= depth) =>
 Unsigned (len + depth) -> -- ^ x
 Unsigned (len + depth) -> -- ^ y
 Unsigned ((len + depth) * 2) -- ^ x * y
karatsuba a b = karatsuba_ @len @stages @depth (toUNat SNat) a b

-- Karatsuba time
karatsuba_ :: forall len stages depth. (KnownNat len, KnownNat stages, KnownNat depth, P.Mod len (2 ^ stages) ~ 0) =>
 UNat stages ->
 Unsigned (len + depth) ->
 Unsigned (len + depth) ->
 Unsigned ((len + depth) * 2)
karatsuba_ UZero x y = resize x * resize y
karatsuba_ (USucc stagesLeft) x y
 | Dict <- lemma_mod @len @stages
 , Dict <- lemma_mul_div @len @2 =
 let
  shifts = natToNum @(Div len 2)
  -- All the subsequent carry bits will be in the high parts, and that's why we
  -- have to truncate the low parts, and shift only by `@(Div len 2)`.
  xLow, yLow :: Unsigned (Div len 2 + depth)
  xHigh, yHigh :: Unsigned (Div len 2 + depth)
  xLow  = bitCoerce $ resize $ truncateB @_ @(Div len 2) @(Div len 2 + depth) x
  yLow  = bitCoerce $ resize $ truncateB @_ @(Div len 2) @(Div len 2 + depth) y
  xHigh = resize $ shiftR x shifts
  yHigh = resize $ shiftR y shifts
  z0, z1, z2, z3 :: Unsigned (len + depth * 2)
  z2 = karatsuba_ @(Div len 2) stagesLeft xHigh yHigh
  z0 = karatsuba_ @(Div len 2) stagesLeft xLow yLow
  z3 = karatsuba_ @(Div len 2) stagesLeft (xHigh + xLow) (yHigh + yLow)
  z1 = z3 - z2 - z0
 in
  resize z0 +
  shiftL (resize z1) (natToNum @(Div len 2)) +
  shiftL (resize z2) (natToNum @len)

-- -- * Streaming implementations

karatsuba_streamingSigned :: forall len streamingStages combStages dom.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat len, KnownNat streamingStages, KnownNat combStages,
 P.Mod len (2 ^ (combStages + streamingStages)) ~ 0, P.Mod len (2 ^ streamingStages) ~ 0) =>
 Signal dom (Signed (len + 1)) ->
 Signal dom (Signed (len + 1)) ->
 Signal dom (Signed (len * 2 + 1))
karatsuba_streamingSigned s1 s2 =
 fmap addSign $ bundle ((toSignal $ antiDelay @(3 ^ streamingStages) SNat sign), res)
 where
  addSign :: (Bit, Unsigned (len * 2)) -> Signed (len * 2 + 1)
  addSign (s, v) = (if s == low then id else negate) $ bitCoerce $ resize v
  res :: Signal dom (Unsigned (len * 2))
  res  = karatsuba_streaming @len @streamingStages @combStages @(combStages + streamingStages) (fmap signedToUnsigned s1) (fmap signedToUnsigned s2)
  sign :: DSignal dom (3 ^ streamingStages) Bit
  sign = delayedI low $ fromSignal $ fmap (\(a,b) -> msb a `xor` msb b) $ bundle (s1, s2)

-- |A sequential implementation of the Karatsuba algorithm for multiplication.
-- It supports recursion on the size of its arguments, dividing the length
-- by 2 each time it recurs, relying on both sequential and combinatorial
-- subcircuits, which depths are configurable at type-level.
-- The circuit is usable each `3 ^ streamingStages` cycles, and is aligned
-- on `[0, 3 ^ streamingStages, ...]. Any values passed between these two points
-- in time will be discarded. All values produced between these two points in
-- time is unusable.
-- __Example:__
-- @
-- karatsuba_streaming @256 @2 @2 @4
-- @
-- will produce a sequential circuit with latency `9 = 3 ^ 2` that is able
-- to multiply two 256-bit unsigned numbers.
karatsuba_streaming :: forall len streamingStages combStages depth dom.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat combStages, KnownNat len, KnownNat depth,
  KnownNat streamingStages, P.Mod len (2 ^ (combStages + streamingStages)) ~ 0, combStages + streamingStages <= depth,
  P.Mod len (2 ^ (streamingStages)) ~ 0) =>
  Signal dom (Unsigned len) ->
  Signal dom (Unsigned len) ->
  Signal dom (Unsigned (len * 2))
karatsuba_streaming s1 s2 =
 fmap resize $ karatsuba_streaming_ @len @streamingStages @combStages @depth (toUNat (SNat :: SNat streamingStages))
  (fmap resize s1) (fmap resize s2)

type KaratsubaCounter stages = (Index 3, Index (3 ^ (stages - 1)))

-- The `depth` type-level natural is needed for the carry. Without it, additions
-- can go awry. I chose to use `depth` all throughout the circuit, but with
-- more clever type-level plays, it's possible to manage the depth
-- automatically.
karatsuba_streaming_ :: forall len streamingStages combStages depth dom.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat combStages, KnownNat len,
  KnownNat streamingStages, KnownNat depth,
  P.Mod len (2 ^ (combStages + streamingStages)) ~ 0) =>
 UNat streamingStages ->
 Signal dom (Unsigned (len + depth)) ->
 Signal dom (Unsigned (len + depth)) ->
 Signal dom (Unsigned ((len + depth) * 2))
karatsuba_streaming_ UZero s1 s2 = register 0 $
 fmap (\(x, y) -> karatsuba_ @len @combStages @depth (toUNat (SNat :: SNat combStages)) x y) $ bundle (s1, s2)
karatsuba_streaming_ (USucc streamingStagesLeft) x y
 | Dict <- lemma_pow @(streamingStages - 1)
 , Dict <- lemma_mod @len @(combStages + streamingStages)
 , Dict <- lemma_mul_div @len @2 =
 let
  shifts = natToNum @(Div len 2)
  xLow, yLow :: Signal dom (Unsigned (Div len 2 + depth))
  xHigh, yHigh :: Signal dom (Unsigned (Div len 2 + depth))
  xLow  = fmap (bitCoerce . resize . truncateB @_ @(Div len 2) @(Div len 2 + depth)) x
  yLow  = fmap (bitCoerce . resize . truncateB @_ @(Div len 2) @(Div len 2 + depth)) y
  xHigh = fmap resize $ fmap (\q -> shiftR q shifts) x
  yHigh = fmap resize $ fmap (\q -> shiftR q shifts) y
  counter :: Signal dom (KaratsubaCounter streamingStages)
  counter = register (0,0) $ fmap countSucc counter
  s1 = bundle (xHigh, yHigh)
  s2 = toSignal $ delayedI @(3 ^ (streamingStages - 1)) (0,0) $ fromSignal $ bundle (xLow, yLow)
  s3 = toSignal $ delayedI @(2 * 3 ^ (streamingStages - 1)) (0,0) $ fromSignal $ bundle (yHigh + yLow, xHigh + xLow)
  spec :: Signal dom ((Unsigned (Div len 2 + depth), Unsigned (Div len 2 + depth)))
  spec = head <$> (fmap (\(a,b,c,(i,_)) -> rotateLeft (a :> b :> c :> Nil) i) $ bundle (s1,s2,s3,counter))
  o = (uncurry $ karatsuba_streaming_ @_ @_ @combStages @depth streamingStagesLeft) $ unbundle spec
  res1 :: DSignal dom (3 ^ (streamingStages - 1)) (Unsigned ((Div len 2 + depth) * 2))
  res1 = delayedI 0 $ fromSignal o
  res2 :: DSignal dom (2 * ((3 ^ (streamingStages - 1)))) (Unsigned ((Div len 2 + depth) * 2))
  res2 = delayedI 0 res1
  res4 = fmap (\(z2, z0, z3) -> (z0, z3  - z2 - z0, z2))
   $ bundle (o,
             toSignal $ antiDelay @((3 ^ (streamingStages - 1))) SNat res1,
             toSignal $ antiDelay @((2 * 3 ^ (streamingStages - 1))) SNat res2)
 in
  fmap (\(a, b, c) -> resize a +
  shiftL (resize b) (natToNum @(Div len 2)) +
  shiftL (resize c) (natToNum @len)) $ res4

-- * Delayed implementations.

-- |This implementation is the same as the one above (or at least it should)
-- but it uses `DSignal` instead of `Signal` for easier tracking.
karatsuba_streaming_D :: forall len streamingStages combStages depth dom d.
 (KnownDomain dom, HiddenClockResetEnable dom, KnownNat combStages, KnownNat len,
  KnownNat streamingStages, KnownNat depth,
  P.Mod len (2 ^ (combStages + streamingStages)) ~ 0) =>
 UNat streamingStages ->
 DSignal dom d (Unsigned (len + depth)) ->
 DSignal dom d (Unsigned (len + depth)) ->
 DSignal dom (d + 3 ^ streamingStages) (Unsigned ((len + depth) * 2))
karatsuba_streaming_D UZero s1 s2 =
 delayedI 0 $ fmap (\(x, y) -> karatsuba_ @len @combStages @depth (toUNat (SNat :: SNat combStages)) x y) $ DB.bundle (s1, s2)
karatsuba_streaming_D (USucc streamingStagesLeft) x y
 | Dict <- lemma_pow @(streamingStages - 1)
 , Dict <- lemma_mod @len @(combStages + streamingStages)
 , Dict <- lemma_mul_div @len @2 =
 let
  shifts = natToNum @(Div len 2)
  xLow, yLow :: DSignal dom d (Unsigned (Div len 2 + depth))
  xHigh, yHigh :: DSignal dom d (Unsigned (Div len 2 + depth))
  xLow  = fmap (bitCoerce . resize . truncateB @_ @(Div len 2) @(Div len 2 + depth)) x
  yLow  = fmap (bitCoerce . resize . truncateB @_ @(Div len 2) @(Div len 2 + depth)) y
  xHigh = fmap resize $ fmap (\q -> shiftR q shifts) x
  yHigh = fmap resize $ fmap (\q -> shiftR q shifts) y
  spec :: DSignal dom d ((Unsigned (Div len 2 + depth), Unsigned (Div len 2 + depth)))
  counter :: DSignal dom (d + 1) (KaratsubaCounter streamingStages)
  counter = delayedI (0,0) $ fmap countSucc counter
  s1 = DB.bundle (xHigh, yHigh)
  s2 = delayedI @(3 ^ (streamingStages - 1)) (0,0) $ fromSignal $ bundle (xLow, yLow)
  s3 = delayedI @(2 * 3 ^ (streamingStages - 1)) (0,0) $ fromSignal $ bundle (yHigh + yLow, xHigh + xLow)
  spec = head <$> (fmap (\(a,b,c,(i,_)) -> rotateLeft (a :> b :> c :> Nil) i) $ DB.bundle (s1,s2,s3,counter))
  o = (uncurry $ karatsuba_streaming_D @_ @_ @combStages @depth streamingStagesLeft) $ DB.unbundle spec
  res1 :: DSignal dom (2 * 3 ^ (streamingStages - 1)) (Unsigned ((Div len 2 + depth) * 2))
  res1 = delayedI 0 o
  res2 :: DSignal dom (3 ^ (streamingStages)) (Unsigned ((Div len 2 + depth) * 2))
  res2 = delayedI 0 res1
  res4 = fmap (\(z2, z0, z3) -> (z0, z3  - z2 - z0, z2))
   $ DB.bundle (delayedI @((2 * 3 ^ (streamingStages - 1))) 0 o,
                delayedI @((3 ^ (streamingStages - 1))) 0 res1,
                res2)
 in
  fmap (\(a, b, c) -> resize a +
  shiftL (resize b) (natToNum @(Div len 2)) +
  shiftL (resize c) (natToNum @len)) $ res4
