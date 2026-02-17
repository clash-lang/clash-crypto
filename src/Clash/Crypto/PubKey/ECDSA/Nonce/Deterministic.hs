{-|
Module      : Clash.Crypto.PubKey.ECDSA.Nonce.Deterministic
Copyright   : Copyright © 2025-2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

A streaming implementation generating a nonce for deterministic ECDSA
according to [FIPS 186-5](https://doi.org/10.6028/NIST.FIPS.186-5).
-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}

module Clash.Crypto.PubKey.ECDSA.Nonce.Deterministic
  ( deriveNonce
  ) where

import Clash.Prelude.Safe
import Clash.Signal.Channel
import Clash.Signal.DataStream

import Data.Constraint.Nat.Extra
  (CancelMultiple, DivRuMulGE, DivRuMulGeOne, MaxOverLE, AddMod)
import GHC.TypeNats.Proof (Rewrite(..), using)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Calculator.Modulo (ModSize, ℤₘ)
import Clash.Crypto.Hash.SHA
  (SHA, BlockSize, MessageDigestSize, Digest, KnownSHA(..), SHAFacts(..))
import Clash.Crypto.MAC.HMAC (hmacE)

-- | An implementation of the deterministic nonce generation for ECDSA, as
-- described in Appendix A.3.3. The result is outputted *before* computing its
-- power (step 4.4) since it makes sharing resources easier in the context of a
-- circuit. This implementation starts at step 1.4, triggers on complete
-- reception of the seed material and doesn't check the length of the seed. The
-- provided @seed_material@ must be @ModSize p + MessageDigestSize alg@ bits long.
deriveNonce ∷
  ∀ (dom ∷ Domain). HiddenClockResetEnable dom ⇒
  ∀ (p ∷ Nat) → KnownNat p ⇒
  ( 1 ≤ p
  , 1 <= ModSize p `Div` 8
  , 1 <= ModSize p
  , ModSize p `Mod` 8 ~ 0
  ) ⇒
  ∀ (alg ∷ SHA) → KnownSHA alg ⇒
  -- | the @seed_material@
  DataStream dom () () (BitVector 8) →
  -- | output from the hash algorithm.
  Channel dom (Digest alg) →
  -- | @k@ (the nonce to be multiplied afterwards, → k ^ 16)
  -- and the data stream going to the hash algorithm
  (Channel dom (ℤₘ p), DataStream dom () (Index 8) (BitVector 8))
deriveNonce p alg seedMaterial shaOutput
  = (Channel output.result, register NoData hmacOutput)
 where
  lastRes ∷ Channel dom (Digest alg)
  hmacOutput ∷ DataStream dom () (Index 8) (BitVector 8)
  (lastRes, hmacOutput)
    | SHAFacts ← knownSHA alg
    = hmacE alg (register NoData $ output.hmacInput) shaOutput

  output ∷ Signal dom (NonceOutput alg p)
  output | SHAFacts ← knownSHA alg = mealy (~~>) initialState
    $ NonceInput <$> newsfeed lastRes <*> seedMaterial

  maxBoundPk
    | SHAFacts ← knownSHA alg
    = natToNum @(ModSize p `Div` 8 - 1)

  maxBoundHash
    | SHAFacts ← knownSHA alg
    = natToNum @(MessageDigestSize alg `Div` 8 - 1)

  initialState ∷ NonceState alg p
  initialState
    | SHAFacts ← knownSHA alg
    , Rewrite ← using @(CancelMultiple (MessageDigestSize alg) 8)
    = NonceState
      { nonceStage  = NonceIdle
      , frameStage  = KeySend
      , currentV    = bitCoerce $ repeat (0x01 ∷ BitVector 8)
      , currentKey  = 0
      , currentSeed = (0, 0)
      , sendCounter = minBound
      , resultAcc   = repeat $ errorX "undefined initial result accumulator"
      , isResult    = False
      }

  (~~>) ∷
    NonceState alg p →
    NonceInput alg →
    (NonceState alg p, NonceOutput alg p)

  -- Wait for a new message to be processed. Upon receiving a Start frame,
  -- starts retrieving seed_material.
  s@(nonceStage → NonceIdle) ~~> i = case i.inputSeed of
    Start () val → baseResult s
      { nonceStage  = NonceRetrieveSeed
      , currentSeed = seedUpdate s val
      , resultAcc   = case knownSHA alg of SHAFacts → repeat undefined
      , isResult    = False
      }
    _ → baseResult s

  s@(nonceStage → NonceRetrieveSeed) ~~> i = case i.inputSeed of
    Middle val → (s { currentSeed = seedUpdate s val }, baseOutput s)
    End () val →
      ( s { nonceStage  = InitFirst
          , sendCounter = case knownSHA alg of SHAFacts → minBound
          , currentSeed = seedUpdate s val
          }
      , (baseOutput s) { hmacInput = firstByte s }
      )
    _ → baseResult s

  -- Process data coming from HMAC and use it as the next `Key` or `V`.
  s0 ~~> (inputLast → Just val) = case s0.nonceStage of
    NonceLoopCheck i
      | SHAFacts ← knownSHA alg
      , res /= 0 && res < natToNum @p && i == maxBound
      → ( initialState { isResult = True , resultAcc = s1.resultAcc }
        , NonceOutput { result = Fresh $ bitCoerce res , hmacInput = NoData }
        )
    _ → ( outS
        , (baseOutput outS) { hmacInput = firstByte outS }
        )
   where
     s1 | SHAFacts ← knownSHA alg
        , Rewrite ← using @(DivRuMulGeOne (ModSize p) (MessageDigestSize alg))
        = s0 { nonceStage = case s0.nonceStage of
                 NonceIdle         → NonceRetrieveSeed
                 NonceRetrieveSeed → InitFirst
                 InitFirst         → InitSecond
                 InitSecond        → InitThird
                 InitThird         → InitFourth
                 InitFourth        → NonceLoopCheck minBound
                 NonceLoopCheck i
                   | i == maxBound → NonceLoopKey
                   | otherwise     → NonceLoopCheck (satSucc SatBound i)
                 NonceLoopKey      → NonceLoopV
                 NonceLoopV        → NonceLoopCheck minBound
             , sendCounter = minBound
             , frameStage = KeySend
             , resultAcc = s0.resultAcc <<+ val
             }

     outS = case s0.nonceStage of
       InitSecond       → s1 { currentV   = val }
       InitFourth       → s1 { currentV   = val }
       NonceLoopCheck _ → s1 { currentV   = val }
       NonceLoopV       → s1 { currentV   = val }
       _                → s1 { currentKey = val }

     res = getHighPart s1.resultAcc

  -- Wait for HMAC to finish computing.
  s ~~> _
    | s.sendCounter == maxBoundHash
    , lastFrame s.nonceStage == s.frameStage
    = (s, baseOutput s)

  -- Divide the data into frames for HMAC.
  s0 ~~> _
    | let eqcmh = s0.sendCounter == maxBoundHash
          eqcmk = s0.sendCounter == maxBoundPk
          neqsl = s0.frameStage /= lastFrame s0.nonceStage
          eqssf = s0.frameStage == SeedFirst
    , s0.frameStage == ByteSend || eqcmh && neqsl || eqcmk && eqssf
    = (s1, (baseOutput s1) { hmacInput = hmacIn })
   where
    s1 = s0
      { frameStage = succ s0.frameStage
      , sendCounter = case knownSHA alg of SHAFacts → minBound
      }

    hmacIn = case s1.frameStage of
     ByteSend → case s1.nonceStage of
       InitFirst    → Middle 0
       InitThird    → Middle 1
       NonceLoopKey → End () 0
       _            → error "These states don't use an extra byte"
     _ | SHAFacts ← knownSHA alg → Middle $ frameValue s1 0 s1.frameStage

  s0 ~~> _ = (s1, (baseOutput s1) { hmacInput = hmacIn })
   where
    s1 | SHAFacts ← knownSHA alg
       , SNat ∷ SNat n ← SNat @(MessageDigestSize alg `Div` 8)
       , Rewrite ← using @(MaxOverLE (ModSize p `Div` 8) n 1)
       = s0 { sendCounter = satSucc SatBound s0.sendCounter }
    val = frameValue s0 s1.sendCounter s1.frameStage
    hmacIn
      | s1.frameStage  == lastFrame s1.nonceStage
      , s1.sendCounter == maxBoundHash
      = End () val

      | otherwise
      = Middle val

  toV ∷
    (BitPack a, BitSize a ~ MessageDigestSize alg) ⇒
    a → Vec (MessageDigestSize alg `Div` 8) (BitVector 8)
  toV | SHAFacts ← knownSHA alg
      , Rewrite ← using @(CancelMultiple (MessageDigestSize alg) 8)
      = bitCoerce

  toVpK ∷
    (BitPack a, BitSize a ~ ModSize p) ⇒
    a → Vec (ModSize p `Div` 8) (BitVector 8)
  toVpK | SHAFacts ← knownSHA alg
        , Rewrite ← using @(CancelMultiple (ModSize p) 8)
        = bitCoerce

  firstByte s
    | SHAFacts ← knownSHA alg
    = Start (natToNum @(MessageDigestSize alg `Div` 8))
    $ toV s.currentKey !! (0 ∷ Index (MessageDigestSize alg `Div` 8))

  seedUpdate s val
    | SHAFacts ← knownSHA alg
    , Rewrite ← using @(AddMod (ModSize p) (MessageDigestSize alg) 8)
    , Rewrite ← using @(CancelMultiple (ModSize p + MessageDigestSize alg) 8)
    , SNat ∷ SNat n ← SNat @((ModSize p + MessageDigestSize alg) `Div` 8)
    = let seedAsVec ∷ Vec n (BitVector 8)
          seedAsVec = bitCoerce s.currentSeed
       in bitCoerce $ seedAsVec <<+ val

  getHighPart ∷
    Vec (ModSize p `DivRU` MessageDigestSize alg) (Digest alg) →
    Unsigned (ModSize p)
  getHighPart
    | SHAFacts ← knownSHA alg
    , Rewrite ← using @(DivRuMulGE (ModSize p) (MessageDigestSize alg))
    = fst . bitCoerce @_
        @(_, BitVector (_ * MessageDigestSize alg - ModSize p))

  -- Generic output for the Mealy machine.
  baseResult x = (x, baseOutput x)

  baseOutput ∷ NonceState alg p → NonceOutput alg p
  baseOutput s = NonceOutput { result = r, hmacInput = NoData }
   where
    r = if s.isResult then Old $ bitCoerce $ getHighPart s.resultAcc else None

  frameValue s ctr | SHAFacts ← knownSHA alg = \case
    KeySend    → toV s.currentKey !! ctr
    FillerSend → errorX "Filler data"
    VSend      → toV s.currentV !! ctr
    SeedFirst  → toVpK (fst s.currentSeed) !! ctr
    SeedLast   → toV (snd s.currentSeed) !! ctr
    _          → error "Nonce generation: should never be reached"

  -- Returns the last frame associated to a step of the algorithm.
  lastFrame = \case
    InitFirst        → SeedLast
    InitSecond       → VSend
    InitThird        → SeedLast
    InitFourth       → VSend
    NonceLoopCheck _ → VSend
    NonceLoopKey     → ByteSend
    NonceLoopV       → VSend
    _                → error
      "NonceIdle and NonceRetrieveSeed don't send data to HMAC."

-- | Internal state of a round.
data SendState
  = KeySend
  | FillerSend
  | VSend
  | ByteSend
  | SeedFirst
  | SeedLast
  deriving (Eq, Show, Generic, NFDataX, Enum)

-- | The different stages of the deterministic nonce generation algorithm. Apart
-- from `NonceIdle` and `NonceRetrieveSeed`, they bear a one-to-one relationship
-- with steps 1.6 to 1.9, 4.2.1, 4.5, and 4.6 of the algorithm.
data NonceStage alg bitsize
  = InitFirst -- 1.6
  | InitSecond -- 1.7
  | InitThird -- 1.8
  | InitFourth -- 1.9
  | NonceLoopCheck (Index (bitsize `DivRU` MessageDigestSize alg))
  | NonceLoopKey -- 4.2.1
  | NonceLoopV -- 4.5, 4.6
  | NonceIdle
  | NonceRetrieveSeed
  deriving (Eq, Show, Generic, NFDataX)

-- | The inputs to the deterministic nonce generation's Mealy machine.
data NonceInput alg = NonceInput
  { -- | The last digest produced by HMAC.
    inputLast ∷ Maybe (Digest alg)
  , -- | seed_material, as byte-sized frames.
    inputSeed ∷ Frame () () (BitVector 8)
  }

-- | The outputs of the deterministic nonce generation's Mealy machine.
data NonceOutput alg p = NonceOutput
  { -- | The input frames for HMAC, computed from the following values:
    -- * The HMAC key
    -- * The V value
    -- * The private key
    -- * The message hash
    hmacInput ∷ Frame (Index ((BlockSize alg `Div` 8) + 1)) () (BitVector 8)
  , -- | The result of the computation.
    result ∷ Content (ℤₘ p)
  }

-- | The internal state of the deterministic nonce generation's Mealy machine.
data NonceState alg p = NonceState
  { -- | The current step in the algorithm.
    nonceStage ∷ NonceStage alg (ModSize p)
  , -- | The frame type currently being sent.
    frameStage ∷ SendState
  , -- | The current HMAC key.
    currentKey ∷ Digest alg
  , -- | The current V.
    currentV ∷ Digest alg
  , -- | seed_material
    currentSeed ∷ (ℤₘ p, Digest alg)
  , -- | A counter tracking how many bytes have been processed for a
    -- given frame.
    sendCounter ∷
      Index (Max (ModSize p `Div` 8) (MessageDigestSize alg `Div` 8))
  , -- | The accumulated results from step 4.2.2.
    resultAcc ∷ Vec (ModSize p `DivRU` MessageDigestSize alg) (Digest alg)
  , -- | Is the accumulated result the final result of the computation?
    isResult ∷ Bool
  } deriving Generic

instance
  ( KnownNat p, KnownNat (MessageDigestSize alg)
  , 1 <= p, 1 <= MessageDigestSize alg
  ) ⇒ NFDataX (NonceState alg p)
