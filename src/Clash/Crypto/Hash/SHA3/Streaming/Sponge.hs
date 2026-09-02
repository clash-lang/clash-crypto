{-|
Module      : Clash.Crypto.Hash.SHA3.Streaming.Sponge
Copyright   : Copyright © 2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Definitions of ciruits for the sponge function.
-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE LambdaCase #-}

module Clash.Crypto.Hash.SHA3.Streaming.Sponge where

import Clash.Prelude.Safe

import Data.Kind (Type)
import Data.Maybe (fromMaybe, isJust)
import Data.Data (Proxy(Proxy))
import Data.Type.Ord
import Data.Type.Bool (If)
import GHC.TypeNats.Proof (Rewrite (..), QED (using), type (==))
import GHC.TypeLits.KnownNat (KnownBool)
import Language.Haskell.Unicode (type (≤))

import Data.Constraint.Nat.Extra
  ( DDiv
  , CancelMultiple
  , KeepsPositiveIfMultiple
  , LtImpliesLE
  , DividentLTRemTimesDivider )
import Clash.Signal.Channel
import Clash.Signal.DataStream (DataStream, Frame (..), mayD, isStartFrame)
import Clash.Crypto.Hash.SHA3.State (KnownStateL, StateSize, State, toState, toArray)
import Clash.Crypto.Hash.SHA3.Functions.Permutations (truncLT, trunc)

-- | Number of squeezes we need to perform for digest size and algorithm rate.
type SqueezeCount ∷ Nat → Nat → Nat
type SqueezeCount d r = d `Div` r + If (d `Mod` r == 0) 0 1

-- | State of the sponge circuit.
data SpongeState (r ∷ Nat) (d ∷ Nat) =
    SpongeInit
  | SpongeAbsorb Bool
  | SpongeSqueeze (Index (SqueezeCount d r))
  deriving (Show, Generic, NFDataX)

-- | A circuit that implements the sponge function in a streaming version.
-- The input is streamed in frames and it is processed in nr cycles
-- by the given absorb function. Then it is squeezed using the same function
-- to produce a result of length d.
-- It emits a result in @inputFramesCount + (nr * SqueezeCount d r) + 1@ cycles.
spongeController ∷
  ∀ (n ∷ Nat) (dom ∷ Domain) (l ∷ Nat) (d ∷ Nat).
  (KnownNat n, 1 ≤ n, HiddenClockResetEnable dom, KnownStateL l) ⇒
  (KnownNat d, 1 ≤ d) ⇒
  ∀ (r ∷ Nat) →
    ( KnownNat r, 1 ≤ r, r < StateSize l
    , Mod r n ~ 0, KnownBool (d `Mod` r == 0)
    ) ⇒
  -- ^ The absorb rate. This must be a positive integer less than the state size.
  ∀ (nr ∷ Nat). (KnownNat nr, 2 ≤ nr) ⇒
  (State l → Index nr → State l) →
    -- ^ The function to be used for absorbing and squeezing.
  DataStream dom () () (BitVector n) →
  -- ^ The streamed input.
  Channel dom (BitVector d)
  -- ^ The output in the form of a channel.
spongeController r f input
  | Rewrite ← using @(CancelMultiple r n)
  , Rewrite ← using @(KeepsPositiveIfMultiple r n) =
  let
    -- Keep all the incoming frames in a queue
    collector ∷ Signal dom (Vec (DDiv r n - 1) (BitVector n))
    collector = register (repeat zeroBits) $
      liftA2 (\clctr → mayD clctr (clctr <<+)) collector input
    
    -- Keep track of the size of the queue
    collectorSize ∷ Signal dom (Index (DDiv r n))
    collectorSize = register (0 ∷ Index (DDiv r n)) $
      liftA2 newSize collectorSize input

    newSize size = \case
      Idle     → 0
      Start {} → 1
      Stretch  → size
      _        → satSucc SatWrap size

    -- The DataPath:
    -- dataPath's init state
    initState = repeat (repeat zeroBits)
    -- Preprocess input function
    preprocess ∷ State l → BitVector r → State l
    preprocess s vec
      | Rewrite ← using @(LtImpliesLE r (StateSize l)) =
      let (rlens ∷ BitVector r, rest ∷ BitVector (StateSize l - r)) =
                                                            split (toArray s)
      in toState $ (vec `xor` rlens) ++# rest
    -- Postprocess output function
    postProcess ∷ State l → BitVector r
    postProcess = truncLT r . toArray
    -- Input signal from collector and input
    concatCollector cl fr = concatBitVector# cl ++# mayD zeroBits id fr
    dataInput ∷ Signal dom (BitVector r)
    dataInput = liftA2 concatCollector collector input
    -- dataPath input (control signals and data)
    dataPathInput ∷ Signal dom (ApplyNControl, BitVector r)
    dataPathInput = bundle (fresInput, dataInput)
    -- dataPath result
    dataResult ∷ Signal dom (Maybe (BitVector r))
    dataResult = applyN @dom initState f preprocess postProcess dataPathInput
    dataPathOutSignals ∷ Signal dom (Index (Div r n), Bool)
    dataPathOutSignals = bundle (collectorSize, isJust <$> dataResult)

    -- Controller's output
    controller ∷ Signal dom (ApplyNControl, Bool)
    controller = mealy transfer SpongeInit (bundle (input, dataPathOutSignals))
    fresInput = fst <$> controller
    publish = delay False $ snd <$> controller

    transfer ∷
      SpongeState r d →
      (Frame () () (BitVector n), (Index (Div r n), Bool)) →
      (SpongeState r d, (ApplyNControl, Bool))
    -- Init state
    -- Accepting a single frame only makes sense if r = n.
    -- In that case the collector is empty and we go directly to squeezing.
    transfer SpongeInit (End {}, _) | isJust $ sameNat @r @n Proxy Proxy
      = (SpongeSqueeze maxBound, (FirstInput, False))
    transfer SpongeInit (inputf, _) =
      if isStartFrame inputf
      then (SpongeAbsorb False, (NoInput, False))
      else (SpongeInit, (NoInput, False))
    -- Absorb state
    transfer (SpongeAbsorb sentFirst) (Stretch, _)
      = (SpongeAbsorb sentFirst, (NoInput, False))
    transfer (SpongeAbsorb sentFirst) (Middle _, (fc, _)) | fc == maxBound
      = (SpongeAbsorb True, (if sentFirst then Input else FirstInput, False))
    transfer (SpongeAbsorb sentFirst) (Middle _, _)
      = (SpongeAbsorb sentFirst, (NoInput, False))
    transfer (SpongeAbsorb sentFirst) (End {}, (fc, _)) | fc == maxBound
      = (SpongeSqueeze maxBound, (if sentFirst then Input else FirstInput, False))
    transfer (SpongeAbsorb _) _ -- Error state
      = errorX "spongeController: unexpected state"
    -- Squeeze state
    transfer (SpongeSqueeze 0) (_, (_, True))
      = (SpongeInit, (NoInput, True))
    transfer (SpongeSqueeze i) (_, (_ ,True))
      = (SpongeSqueeze (satPred SatError i), (InternalInput, False))
    transfer (SpongeSqueeze i) (_, (_, False))
      = (SpongeSqueeze i, (NoInput, False))

    -- Accumulator of the datapath's outputs
    finalZ ∷ Signal dom (Vec (SqueezeCount d r) (BitVector r))
    finalZ = register (repeat zeroBits) $
      liftA2 (\v → maybe v (v <<+)) finalZ dataResult

    concatAndTrunc ∷ Vec (SqueezeCount d r) (BitVector r) → BitVector d
    concatAndTrunc z
      | Rewrite ← using @(DividentLTRemTimesDivider d r)
      = trunc d (concatBitVector# z)
    -- Trunc_d(finalZ)
    truncZ = concatAndTrunc <$> finalZ
    -- Publish truncZ whenever we get a publish signal from the controller
    result = liftA2 (\enbl res → if enbl then Just res else Nothing) publish truncZ
  in cachedFromMaybe result

-- | The controls for the data path.
data ApplyNControl =
    FirstInput
  | Input
  | NoInput
  | InternalInput
  deriving (Show, Generic, NFDataX)

-- | The data path's state.
-- Invariant: If index = 0 then the value is ready
data ApplyState v nr = ApplyState v (Maybe (Index nr))
  deriving (Show, Generic, NFDataX)

-- | A component that processes state over multiple cycles
-- by applying repeateadly a computation.
-- It will emmit the result in @nr + 1@ cycles.
-- The state can be combined with input data using a function g
-- and the output can be constructed from the state using a function h.
-- The input of the multi-cycle computation, depends on the input control:
--
-- * @FirstInput@: the input is @g initialState input@
-- * @Input@: the input is @g state input@
-- * @InternalInput@: the input is the current state
-- * @NoInput@: No computation starts
-- The output at cycle @nr + 1@ is @h state@.
applyN ∷
  ∀ (dom ∷ Domain). HiddenClockResetEnable dom ⇒
  ∀ (nr ∷ Nat). (KnownNat nr, 2 ≤ nr) ⇒
  -- ^ Number of rounds to apply the computation function.
  ∀ (v ∷ Type). NFDataX v ⇒
  -- ^ Type of the internal data.
  ∀ (inType ∷ Type).
  -- ^ Type of the input data.
  ∀ (outType ∷ Type).
  -- ^ Type of the output data.
  v →
  -- ^ Initial state.
  (v → Index nr → v) →
  -- ^ The function f that is applied in each round.
  (v → inType → v) →
  -- ^ The function g to combine input with state.
  (v → outType) →
  -- ^ The function h to create output from state.
  Signal dom (ApplyNControl, inType) →
  -- ^ Input signal: a pair of control and input data.
  Signal dom (Maybe outType)
  -- ^ Output signal: Will contain output data when the computation is done.
applyN initialState f pre post input =
  moore nextState out (ApplyState initialState Nothing) input
 where
  nextState (ApplyState s Nothing) (NoInput, _)  = ApplyState s Nothing
  nextState (ApplyState s (Just 0)) (NoInput, _) = ApplyState s Nothing
  nextState (ApplyState s rnd) (cmd, inp)        =
    let i = fromMaybe 0 rnd
        s' = case cmd of
          FirstInput → pre initialState inp
          Input      → pre s inp
          _          → s
    in ApplyState (f s' i) (Just (satSucc SatWrap i))
  out (ApplyState s (Just 0)) = Just (post s)
  out _ = Nothing
