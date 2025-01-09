{-# LANGUAGE AllowAmbiguousTypes #-}
module Clash.Crypto.ECDSA.Utils where

import Clash.Prelude

data ComputationState a =
  Working a
  | Finished
  deriving (Generic, NFDataX)

data WaitState a b = WaitIdle | WaitB a | WaitA b deriving (Generic, NFDataX)

data RepeaterState a = RepeaterIdle | Repeat a deriving (Generic, NFDataX)

repeater :: forall a (dom :: Domain) . (NFDataX a, KnownDomain dom, HiddenClockResetEnable dom) =>
 Signal dom (Maybe a) ->
 Signal dom (Maybe a)
repeater = mealy (~~>) RepeaterIdle
 where
  (~~>) :: RepeaterState a -> Maybe a -> (RepeaterState a, Maybe a)
  RepeaterIdle ~~> Nothing  = (RepeaterIdle, Nothing)
  _            ~~> (Just a) = (Repeat a, Just a)
  (Repeat a)   ~~> Nothing  = (Repeat a, Just a)

data RepeaterNState a = RepeatN a (Unsigned 32) | RepeaterNIdle deriving (Generic, NFDataX)

repeaterN :: forall (n :: Nat) a (dom :: Domain) . (KnownNat n, NFDataX a, KnownDomain dom, HiddenClockResetEnable dom, 1 <= n) =>
 Signal dom a ->
 Signal dom a
repeaterN = mealy (~~>) RepeaterNIdle
 where
  (~~>) :: RepeaterNState a -> a -> (RepeaterNState a, a)
  RepeaterNIdle ~~> a = (RepeatN a (natToNum @n), a)
  (RepeatN _ 1) ~~> a = (RepeatN a (natToNum @n), a)
  (RepeatN a l) ~~> _ = (RepeatN a (l - 1), a)

data CyclerState = CycleN Integer deriving (Generic, NFDataX)

cycler3 :: forall a (dom :: Domain) . (NFDataX a, KnownDomain dom, HiddenClockResetEnable dom) =>
 Signal dom (a ,a, a) ->
 Signal dom a
cycler3 = mealy (~~>) $ CycleN 3
 where
  (~~>) :: CyclerState -> (a, a, a) -> (CyclerState, a)
  CycleN 0 ~~> (_, _, c) = (CycleN 1, c)
  CycleN 1 ~~> (_, b, _) = (CycleN 2, b)
  CycleN _ ~~> (a, _, _) = (CycleN 0, a)

data CyclerMemoryState = CycleMemoryN (Unsigned 32) (Unsigned 2) deriving (Generic, NFDataX)

cycler3memory :: forall n a (dom :: Domain) . (NFDataX a, KnownNat n, 1 <= n, KnownDomain dom, HiddenClockResetEnable dom) =>
 Signal dom (a ,a, a) ->
 Signal dom a
cycler3memory = mealy (~~>) $ CycleMemoryN start 3
 where
  (~~>) :: CyclerMemoryState -> (a, a, a) -> (CyclerMemoryState, a)
  CycleMemoryN 0 0 ~~> (_, _, c)  = (CycleMemoryN start 1, c)
  CycleMemoryN 0 1 ~~> (_, b, _)  = (CycleMemoryN start 2, b)
  CycleMemoryN 0 _ ~~> (a, _, _)  = (CycleMemoryN start 0, a)
  CycleMemoryN left 0 ~~> (_,_,c) = (CycleMemoryN (left - 1) 0, c)
  CycleMemoryN left 1 ~~> (_,b,_) = (CycleMemoryN (left - 1) 1, b)
  CycleMemoryN left _ ~~> (a,_,_) = (CycleMemoryN (left - 1) 2, a)
  start = natToNum @n

data CollectorState a = Collect Integer (a, a, a) | CollectorIdle deriving (Generic, NFDataX)

-- TODO; Obsolete?
collect3 :: forall a (dom :: Domain) . (KnownDomain dom, HiddenClockResetEnable dom, Num a, NFDataX a) =>
 Signal dom a ->
 Signal dom (a, a, a)
collect3 = mealy (~~>) CollectorIdle --bundle (s, t1, t2)
 where
  (~~>) :: CollectorState a -> a -> (CollectorState a, (a, a, a))
  CollectorIdle ~~> a = (Collect 1 (a, a, a), (a, a, a))
  Collect 0 (_, b, c) ~~> l = (Collect 1 (l, b, c), (l, b, c))
  Collect 1 (a, _, c) ~~> l = (Collect 2 (a, l, c), (a, l, c))
  Collect _ (a, b, _) ~~> l = (Collect 0 (a, b, l), (a, b, l))

-- A helper function to wait for two different values.
wait2 :: forall a b (dom :: Domain) . (NFDataX a, NFDataX b, KnownDomain dom, HiddenClockResetEnable dom) =>
 Signal dom (Maybe a) ->
 Signal dom (Maybe b) ->
 Signal dom (Maybe (a, b))
wait2 sa sb = mealy (~~>) WaitIdle $ bundle (sa, sb)
 where
  (~~>) :: WaitState a b -> (Maybe a, Maybe b) -> (WaitState a b, Maybe (a,b))
  WaitIdle ~~> (Just a, Nothing) = (WaitB a, Nothing)
  WaitIdle ~~> (Nothing, Just b) = (WaitA b, Nothing)
  WaitIdle ~~> (Just a, Just b)  = (WaitIdle, Just (a, b))
  WaitIdle ~~> _                 = (WaitIdle, Nothing)
  (WaitA b) ~~> (Nothing, _)     = (WaitA b, Nothing)
  (WaitA b) ~~> (Just a, _)      = (WaitIdle, Just (a, b))
  (WaitB a) ~~> (_, Nothing)     = (WaitB a, Nothing)
  (WaitB a) ~~> (_, Just b)      = (WaitIdle, Just (a, b))

unsignedToSigned :: forall len . KnownNat len => Unsigned len -> Signed (len + 1)
unsignedToSigned = bitCoerce . zeroExtend

signedToUnsigned :: forall len . KnownNat len => Signed (len + 1) -> Unsigned len
signedToUnsigned = bitCoerce . truncateB . abs

