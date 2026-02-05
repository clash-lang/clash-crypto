{-|
Module      : Clash.Crypto.ECDSA.DeterministicNonce
Copyright   : Copyright © 2025-2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

A streaming implementation generating a nonce for deterministic ECDSA from
[FIPS 186-5: Digital Signature Standard (DSS)](https://doi.org/10.6028/NIST.FIPS.186-5)
-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}

module Clash.Crypto.ECDSA.DeterministicNonce (deriveNonce) where

import Clash.Prelude
import Clash.Signal.Channel
import Clash.Signal.DataStream

import Data.Constraint.Nat.Extra
 (CancelMultiple, DivRuMulGE, DivRuMulGeOne, MaxOverLE, AddMod)
import GHC.TypeNats.Proof (Rewrite(..), using)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Hash.SHA
import qualified Clash.Crypto.Calculator.Modulo as M

import Clash.Crypto.MAC.HMAC

-- | An implementation of the deterministic nonce generation for ECDSA described
-- in Appendix A.3.3. The result is outputted *before* computing its power (step
-- 4.4) since it makes sharing resources easier in the context of a circuit.
-- This implementation starts at step 1.4, triggers on complete reception of the
-- seed material and doesn't check the length of the seed.
-- The provided `seed_material` must be `M.ModSize p + MessageDigestSize alg` bits
-- long.
deriveNonce ∷
  ∀ (dom ∷ Domain). HiddenClockResetEnable dom ⇒
  ∀ (p ∷ Nat) → (KnownNat p, 1 ≤ p, 1 <= M.ModSize p `Div` 8, 1 <= M.ModSize p,
                 M.ModSize p `Mod` 8 ~ 0) ⇒
  ∀ (alg ∷ SHA) → KnownSHA alg ⇒
  DataStream dom () () (BitVector 8) →
  -- ^ seed_material
  Channel dom (Digest alg) →
  -- ^ output from the hash algorithm.
  (Channel dom (M.Mod p), DataStream dom () (Index 8) (BitVector 8))
  -- ^ k, the nonce to be multiplied afterwards (→ k ^ 16) and the data stream
  -- going to the hash algorithm.
deriveNonce p alg seedMaterial shaOutput
 | SHAFacts ← knownSHA alg
 , Rewrite  ← using @(CancelMultiple (MessageDigestSize alg) 8)
 , Rewrite  ← using @(CancelMultiple (M.ModSize p) 8)
 , Rewrite  ← using @(AddMod (M.ModSize p) (MessageDigestSize alg) 8)
 , Rewrite  ← using @(CancelMultiple (M.ModSize p + MessageDigestSize alg) 8)
 , Rewrite  ← using @(DivRuMulGE (M.ModSize p) (MessageDigestSize alg))
 , Rewrite  ← using @(DivRuMulGeOne (M.ModSize p) (MessageDigestSize alg))
 , Rewrite  ← using @(MaxOverLE (M.ModSize p `Div` 8) (MessageDigestSize alg `Div` 8) 1)
 = let
  initialState ∷ NonceState alg p
  initialState = NonceState
   { nonceStage  = NonceIdle
   , frameStage  = KeySend
   , currentV    = bitCoerce $ repeat (0x01 ∷ BitVector 8)
   , currentKey  = 0
   , currentSeed = bitCoerce (0 :: Unsigned (M.ModSize p + MessageDigestSize alg))
   , sendCounter = minBound
   , resultAcc   = repeat $ errorX "undefined initial result accumulator"
   , isResult    = False
   }

  toV = bitCoerce @_ @(Vec (MessageDigestSize alg `Div` 8) (BitVector 8))
  toVpK = bitCoerce @_ @(Vec (M.ModSize p `Div` 8) (BitVector 8))

  firstByte s
   = Start (natToNum @(MessageDigestSize alg `Div` 8))
   $ toV s.currentKey !! (0 :: Index (MessageDigestSize alg `Div` 8))

  seedUpdate s val = bitCoerce $ seedAsVec <<+ val
   where
    seedAsVec :: Vec ((M.ModSize p + MessageDigestSize alg) `Div` 8) (BitVector 8)
    seedAsVec = bitCoerce s.currentSeed

  getHighPart ::
    Vec (M.ModSize p `DivRU` MessageDigestSize alg) (Digest alg) ->
    Unsigned (M.ModSize p)
  getHighPart
   = fst
    . bitCoerce @_ @(_, BitVector (_ * MessageDigestSize alg - M.ModSize p))

  -- Generic output for the Mealy machine.
  baseOutput ∷ NonceState alg p → NonceOutput alg p
  baseOutput s = NonceOutput
   { result = if s.isResult
              then Old $ bitCoerce $ getHighPart s.resultAcc
              else None
   , hmacInput = NoData
   }

  maxBoundPk = natToNum @(M.ModSize p `Div` 8 - 1)
  maxBoundHash = natToNum @(MessageDigestSize alg `Div` 8 - 1)

  (~~>) ∷ NonceState alg p → NonceInput alg →
   (NonceState alg p, NonceOutput alg p)

  -- Wait for a new message to be processed. Upon receiving a Start frame,
  -- starts retrieving seed_material.
  s@(nonceStage → NonceIdle) ~~> i =
   case i.inputSeed of
    Start () val -> (nS, baseOutput nS)
     where
      nS  = s { nonceStage  = NonceRetrieveSeed
              , currentSeed = seedUpdate s val
              , resultAcc   = repeat undefined
              , isResult    = False }
    _ -> (s, baseOutput s)

  s@(nonceStage → NonceRetrieveSeed) ~~> i =
   case i.inputSeed of
    Middle val -> (s { currentSeed = seedUpdate s val }, baseOutput s)
    End () val ->
     ( s
       { nonceStage  = InitFirst
       , sendCounter = minBound
       , currentSeed = seedUpdate s val
       }
     , (baseOutput s) { hmacInput = firstByte s }
     )
    _ -> (s, baseOutput s)

  -- Process data coming from HMAC and use it as the next `Key` or `V`.
  s ~~> (inputLast → Just val) =
   let nS = s { nonceStage  = case s.nonceStage of
                  NonceIdle         -> NonceRetrieveSeed
                  NonceRetrieveSeed -> InitFirst
                  InitFirst         -> InitSecond
                  InitSecond        -> InitThird
                  InitThird         -> InitFourth
                  InitFourth        -> NonceLoopCheck minBound
                  NonceLoopCheck i
                    | i == maxBound -> NonceLoopKey
                    | otherwise     -> NonceLoopCheck (satSucc SatBound i)
                  NonceLoopKey      -> NonceLoopV
                  NonceLoopV        -> NonceLoopCheck minBound
              , sendCounter = minBound
              , frameStage  = KeySend
              , resultAcc   = s.resultAcc <<+ val
              }
       outS = case s.nonceStage of
                InitSecond       → nS { currentV   = val }
                InitFourth       → nS { currentV   = val }
                NonceLoopCheck _ → nS { currentV   = val }
                NonceLoopV       → nS { currentV   = val }
                _                → nS { currentKey = val }
       res = getHighPart nS.resultAcc
   in case s.nonceStage of
    NonceLoopCheck i | res /= 0 && res < natToNum @p && i == maxBound ->
     ( initialState
         { isResult = True
         , resultAcc = nS.resultAcc
         }
     , NonceOutput
         { result = Fresh $ bitCoerce res
         , hmacInput = NoData
         }
     )
    _ -> (outS, (baseOutput outS) { hmacInput = firstByte outS } )


  -- Wait for HMAC to finish computing.
  s ~~> _ | s.sendCounter == maxBoundHash
         && lastFrame s.nonceStage == s.frameStage =
   (s, baseOutput s)

  -- Divide the data into frames for HMAC.
  s ~~> _ | s.frameStage == ByteSend
         || (s.sendCounter == maxBoundHash && lastFrame s.nonceStage /= s.frameStage)
         || (s.sendCounter == maxBoundPk   && s.frameStage == SeedFirst) =
   let nS = s { frameStage = succ s.frameStage, sendCounter = minBound }
       hmacIn = case frameStage nS of
        ByteSend → case nS.nonceStage of
          InitFirst    → Middle 0
          InitThird    → Middle 1
          NonceLoopKey → End () 0
          _            → error "These states don't use an extra byte"
        _        → Middle $ frameValue nS 0 nS.frameStage
   in (nS, (baseOutput nS) { hmacInput = hmacIn })

  s ~~> _ = (nS, (baseOutput nS) { hmacInput = hmacIn })
   where
    nS = s { sendCounter = satSucc SatBound s.sendCounter }
    cP | nS.frameStage  == lastFrame nS.nonceStage
      && nS.sendCounter == maxBoundHash = End ()
       | otherwise                      = Middle
    hmacIn = cP $ frameValue s nS.sendCounter nS.frameStage

  frameValue s ctr = \case
   KeySend    → toV s.currentKey !! ctr
   FillerSend → errorX "Filler data"
   VSend      → toV s.currentV !! ctr
   SeedFirst  → toVpK (fst s.currentSeed) !! ctr
   SeedLast   → toV (snd s.currentSeed) !! ctr
   _          → error "Nonce generation: should never be reached"

  output = mealy (~~>) initialState
         $ NonceInput <$> newsfeed lastRes <*> seedMaterial

  (lastRes, hmacOutput)
   = hmacE alg (register NoData $ output.hmacInput) shaOutput
   
 in (Channel output.result, register NoData hmacOutput)

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
 = InitFirst | InitSecond | InitThird | InitFourth -- 1.6, 1.7, 1.8, 1.9
 | NonceLoopCheck (Index (bitsize `DivRU` MessageDigestSize alg))
 | NonceLoopKey | NonceLoopV      -- 4.2.1, 4.5, 4.6
 | NonceIdle | NonceRetrieveSeed
 deriving (Eq, Show, Generic, NFDataX)

-- | The inputs to the deterministic nonce generation's Mealy machine.
data NonceInput alg = NonceInput
 { -- | The last digest produced by HMAC.
   inputLast ∷ Maybe (Digest alg)
   -- | `seed_material`, as byte-sized frames.
 , inputSeed ∷ Frame () () (BitVector 8)
 }

-- | The outputs of the deterministic nonce generation's Mealy machine.
data NonceOutput alg p = NonceOutput
 { -- | The input frames for HMAC, computed from the following values:
   -- * The HMAC key
   -- * The V value
   -- * The private key
   -- * The message hash
   hmacInput ∷ Frame (Index ((BlockSize alg `Div` 8) + 1)) () (BitVector 8)
   -- | The result of the computation.
 , result    ∷ Content (M.Mod p)
 }

-- | The internal state of the deterministic nonce generation's Mealy machine.
data NonceState alg p = NonceState
 { -- | The current step in the algorithm.
   nonceStage  ∷ NonceStage alg (M.ModSize p)
   -- | The frame type currently being sent.
 , frameStage  ∷ SendState
   -- | The current HMAC key.
 , currentKey  ∷ Digest alg
   -- | The current V.
 , currentV    ∷ Digest alg
   -- | `seed_material`
 , currentSeed ∷ (M.Mod p, Digest alg)
   -- | A counter tracking how many bytes have been processed for a given frame.
 , sendCounter ∷ Index (Max (M.ModSize p `Div` 8) (MessageDigestSize alg `Div` 8))
   -- | The accumulated results from step 4.2.2.
 , resultAcc   ∷ Vec (M.ModSize p `DivRU` MessageDigestSize alg) (Digest alg)
   -- | Is the accumulated result the final result of the computation?
 , isResult    ∷ Bool
 } deriving Generic

instance
 (KnownNat p, 1 <= p, KnownNat (MessageDigestSize alg), 1 <= MessageDigestSize alg) ⇒
 NFDataX (NonceState alg p)

-- | Returns the last frame associated to a step of the algorithm.
lastFrame ∷ NonceStage alg bs → SendState
lastFrame = \case
 InitFirst        → SeedLast
 InitSecond       → VSend
 InitThird        → SeedLast
 InitFourth       → VSend
 NonceLoopCheck _ → VSend
 NonceLoopKey     → ByteSend
 NonceLoopV       → VSend
 _                → error "NonceIdle and NonceRetrieveSeed don't send data to HMAC."

