{-|
Module      : Clash.Crypto.ECDSA.DeterministicNonce
Copyright   : Copyright © 2025-2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

A streaming implementation generating a nonce for deterministic ECDSA.
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
 (DivUp, CancelMultiple, DivUpBigger, DivUpBiggerOne)
import GHC.TypeNats.Proof (Rewrite(..), using, )
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Hash.SHA
import qualified Clash.Crypto.Calculator.Modulo as M

import Clash.Crypto.MAC.HMAC

-- | An implementation of the deterministic nonce generation for ECDSA described
-- in Appendix A.3.3 of FIPS 186-5, henceforth referred to as "the algorithm".
-- The result is outputted *before* computing its power (step 4.4) since it
-- makes sharing resources easier in the context of a circuit.
-- This implementation starts at step 1.4 of the algorithm, triggers on complete
-- reception of the seed material and doesn't check the length of the seed. It
-- starts reception on a Start frame and starts executing the algorithm on the
-- End frame. The caller has to check the correct length of the seed before
-- sending (`MessageDigestSize alg * 2`), otherwise the circuit will return a
-- wrong result.
deriveNonce ∷
  ∀ (dom ∷ Domain). HiddenClockResetEnable dom ⇒
  ∀ (p ∷ Nat) → (KnownNat p, 1 ≤ p, 1 <= CLog 2 p) ⇒
  ∀ (alg ∷ SHA) →
   ( KnownSHA alg, Mod (BlockSize alg) 8 ~ 0, 1 ≤ MessageDigestSize alg `Div` 8
   , 8 ≤ BlockSize alg, 2 * MessageDigestSize alg `Mod` 8 ~ 0) ⇒
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
 , Rewrite  ← using @(CancelMultiple (2 * MessageDigestSize alg) 8)
 , Rewrite  ← using @(DivUpBigger (CLog 2 p) (MessageDigestSize alg))
 = let
  initialState ∷ NonceState alg (CLog 2 p)
  initialState = NonceState
   { nonceStage  = NonceIdle
   , chunkStage  = KeySend
   , currentV    = bitCoerce $ repeat (0x01 ∷ BitVector 8)
   , currentKey  = 0
   , currentSeed = bitCoerce $ (0 :: Unsigned (MessageDigestSize alg * 2))
   , sendCounter = minBound
   , resultAcc   = repeat (0 :: BitVector (MessageDigestSize alg))
   }

  toV = bitCoerce @_ @(Vec (MessageDigestSize alg `Div` 8) (BitVector 8))

  firstByte s
   = Start (natToNum @(MessageDigestSize alg `Div` 8))
   $ toV s.currentKey !! (0 :: Index (MessageDigestSize alg `Div` 8))

  seedUpdate s val
   = bitCoerce $ bitCoerce @_ @(Vec 2 (BitVector (MessageDigestSize alg)))
   $ bitCoerce @_ @(Vec (2 * MessageDigestSize alg `Div` 8) (BitVector 8))
     s.currentSeed <<+ val

  getHighPart
   = fst . bitCoerce @_ @(Unsigned (CLog 2 p), BitVector
     (CLog 2 p `DivUp` MessageDigestSize alg * MessageDigestSize alg - CLog 2 p))

  (~~>) ∷ NonceState alg (CLog 2 p) → NonceInput alg →
   (NonceState alg (CLog 2 p), NonceOutput alg p)

  -- Wait for a new message to be processed. Upon receiving a Start frame,
  -- starts retrieving seed_material.
  s@(nonceStage → NonceIdle) ~~> i =
   case i.inputSeed of
    Start () val -> (nS, baseOutput)
     where
      nS  = s { nonceStage  = NonceRetrieveSeed
              , currentSeed = seedUpdate s val }
    _ -> (s, baseOutput)

  s@(nonceStage → NonceRetrieveSeed) ~~> i =
   case i.inputSeed of
    Middle val -> (s { currentSeed = seedUpdate s val }, baseOutput)
    End () val ->
     ( s
       { nonceStage  = InitFirst
       , sendCounter = minBound
       , currentSeed = seedUpdate s val
       }
     , baseOutput { hmacInput = firstByte s }
     )
    _ -> (s, baseOutput)

  -- Process data coming from HMAC and use it as the next `Key` or `V`.
  s ~~> (inputLast → Just val) =
   let nS = s { nonceStage  = nextStage s.nonceStage
              , sendCounter = minBound
              , chunkStage  = KeySend
              , resultAcc   = s.resultAcc <<+ val
              } ∷ NonceState alg (CLog 2 p)
       outS | stageV s.nonceStage = nS { currentV   = val }
            | otherwise           = nS { currentKey = val }
       res = getHighPart nS.resultAcc
   in case s.nonceStage of
    NonceLoopCheck i | res /= 0 && res < natToNum @p && i == maxBound ->
     (initialState, (baseOutput @alg) { result = Just $ bitCoerce res } )
    _ -> (outS, baseOutput { hmacInput = firstByte outS } )


  -- Waiting for HMAC to finish computing.
  s ~~> _ | s.sendCounter == maxBound && lastChunk s.nonceStage == s.chunkStage =
   (s, baseOutput)

  -- Chunk the data into frames for HMAC.
  s ~~> _ | s.chunkStage == ByteSend
         || (s.sendCounter == maxBound && lastChunk s.nonceStage /= s.chunkStage) =
   let nS = s { chunkStage = succ s.chunkStage, sendCounter = minBound }
       hmacIn = case chunkStage nS of
        ByteSend → extraByteFrame alg nS.nonceStage
        _        → Middle $ chunkValue nS 0 nS.chunkStage
   in (nS, baseOutput { hmacInput = hmacIn })

  s ~~> _ = (nS , baseOutput { hmacInput = hmacIn })
   where
    nS = s { sendCounter = satSucc SatBound s.sendCounter }
    cP | nS.chunkStage  == lastChunk nS.nonceStage
      && nS.sendCounter == maxBound = End ()
       | otherwise                  = Middle
    hmacIn = cP $ chunkValue s nS.sendCounter nS.chunkStage

  chunkValue s ctr = \case
   KeySend    → toV s.currentKey        !! ctr
   FillerSend → error "Filler data"
   VSend      → toV s.currentV          !! ctr
   SeedFirst  → toV (fst s.currentSeed) !! ctr
   SeedLast   → toV (snd s.currentSeed) !! ctr
   _          → error "Nonce generation: should never be reached"

  output = mealy (~~>) initialState
         $ NonceInput <$> newsfeed lastRes <*> seedMaterial

  (lastRes, hmacOutput)
   = hmacE alg (register NoData $ output.hmacInput) shaOutput
   
 in (cachedFromMaybe output.result, register NoData hmacOutput)

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
 | NonceLoopCheck (Index (bitsize `DivUp` MessageDigestSize alg))
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
 , result :: Maybe (M.Mod p)
 }

-- | The internal state of the deterministic nonce generation's Mealy machine.
data NonceState alg bs = NonceState
 { -- | The current step in the algorithm.
   nonceStage  ∷ NonceStage alg bs
   -- | The chunk currently being sent.
 , chunkStage  ∷ SendState
   -- | The current HMAC key.
 , currentKey  ∷ Digest alg
   -- | The current V.
 , currentV    ∷ Digest alg
   -- | seed_material
 , currentSeed ∷ (Digest alg, Digest alg)
   -- | A counter tracking how many bytes have been processed for a given
   -- chunk of data.
 , sendCounter ∷ Index (MessageDigestSize alg `Div` 8)
 -- | The accumulated results from step 4.2.2.
 , resultAcc :: Vec (bs `DivUp` MessageDigestSize alg) (Digest alg)
 } deriving Generic

instance
 (KnownNat bs, KnownNat (MessageDigestSize alg), 1 <= MessageDigestSize alg) ⇒
 NFDataX (NonceState alg bs)

-- | Returns the last chunk associated to a step of the algorithm.
lastChunk ∷ NonceStage alg bs → SendState
lastChunk = \case
 InitFirst        → SeedLast
 InitSecond       → VSend
 InitThird        → SeedLast
 InitFourth       → VSend
 NonceLoopCheck _ → VSend
 NonceLoopKey     → ByteSend
 NonceLoopV       → VSend
 _                → error "NonceIdle and NonceRetrieveSeed don't chunk data"

-- | Returns the extra byte frame needed by the algorithm, for the relevant
-- states.
extraByteFrame ∷ forall alg → NonceStage alg bs →
 Frame (Index ((BlockSize alg `Div` 8) + 1)) () (BitVector 8)
extraByteFrame _ = \case
 InitFirst    → Middle 0
 InitThird    → Middle 1
 NonceLoopKey → End () 0
 _            → error "These states don't use an extra byte"

-- Generic output for the Mealy machine.
baseOutput ∷ NonceOutput alg p
baseOutput = NonceOutput
 { result = Nothing
 , hmacInput = NoData
 }

-- Returns the next stage in the algorithm.
nextStage ∷ forall alg bs.
 (KnownNat bs, 1 <= bs, 1 <= MessageDigestSize alg,
  KnownNat (MessageDigestSize alg)) =>
 NonceStage alg bs → NonceStage alg bs
nextStage
 | Rewrite ← using @(DivUpBiggerOne bs (MessageDigestSize alg))
  = \case
 NonceIdle -> NonceRetrieveSeed
 NonceRetrieveSeed -> InitFirst
 InitFirst -> InitSecond
 InitSecond -> InitThird
 InitThird -> InitFourth
 InitFourth -> NonceLoopCheck minBound
 NonceLoopCheck i ->
  if i == maxBound then NonceLoopKey else NonceLoopCheck (satSucc SatBound i)
 NonceLoopKey -> NonceLoopV
 NonceLoopV -> NonceLoopCheck minBound

-- | Is the output of the stage reused as the HMAC key or the `V` value?
stageV ∷ NonceStage alg bs → Bool
stageV InitSecond         = True
stageV InitFourth         = True
stageV (NonceLoopCheck _) = True
stageV NonceLoopV         = True
stageV _                  = False
