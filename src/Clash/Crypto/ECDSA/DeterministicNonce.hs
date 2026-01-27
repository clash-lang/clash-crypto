{-|
Module      : Clash.Crypto.ECDSA.DeterministicNonce
Copyright   : Copyright © 2025 QBayLogic B.V.
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

import Data.Constraint.Nat.Extra (CancelMultiple)
import GHC.TypeNats.Proof (Rewrite(..), using)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Hash.SHA
import qualified Clash.Crypto.Calculator.Modulo as M

import Clash.Crypto.MAC.HMAC

-- | An implementation of the deterministic nonce generation for ECDSA
-- described in Appendix A.3.3 of FIPS 186-5, henceforth referred to as
-- "the algorithm". The result is outputted *before* computing its
-- power (step 4.4) since it makes sharing resources easier in the context of
-- a circuit.
deriveNonce ∷
  ∀ (dom ∷ Domain). HiddenClockResetEnable dom ⇒
  ∀ (p ∷ Nat) → (KnownNat p, 1 ≤ p) ⇒
  ∀ (alg ∷ SHA) →
   (KnownSHA alg, CLog 2 p ~ MessageDigestSize alg, Mod (BlockSize alg) 8 ~ 0,
    1 ≤ MessageDigestSize alg `Div` 8, 8 ≤ BlockSize alg) ⇒
  DataStream dom () (Index 8) (BitVector 8) →
  -- ^ message
  Signal dom (BitVector 8) →
  -- ^ private key
  (Channel dom (M.Mod p), Signal dom Bool)
  -- ^ k, the nonce to be multiplied afterwards (→ k ^ 16) and a reset signal
  -- for the private key.
deriveNonce p alg message pk
 | SHAFacts ← knownSHA alg
 , Rewrite  ← using @(CancelMultiple (MessageDigestSize alg) 8)
 = let
  initialState ∷ NonceState alg
  initialState = NonceState
   { nonceStage  = NonceIdle
   , chunkStage  = KeySend
   , currentV    = bitCoerce $ repeat (0x01 ∷ BitVector 8)
   , currentKey  = 0
   , currentHash = error "Initial hash is undefined"
   , sendCounter = minBound
   }

  toV = bitCoerce @_ @(Vec (MessageDigestSize alg `Div` 8) (BitVector 8))

  firstByte s
   = Start (natToNum @(MessageDigestSize alg `Div` 8))
   $ toV s.currentKey !! (0 :: Index (MessageDigestSize alg `Div` 8))

  (~~>) ∷ NonceState alg → NonceInput alg → (NonceState alg, NonceOutput alg)

  -- Wait for a new message to be processed.
  s@(nonceStage → NonceIdle) ~~> i =
   let out = (outputPassBy i) { shaOutput = None } ∷ NonceOutput alg in
   case i.inputSha of
    Fresh h → (nS, out { hmacInput = firstByte nS } )
     where nS = s { nonceStage  = InitFirst
                  , chunkStage  = KeySend
                  , currentHash = h
                  , sendCounter = minBound
                  }
    _ → (s, out { shaInput = i.inputMessage })

  -- Process data coming from HMAC and use it as the next HMAC key or next V.
  s ~~> i@(inputLast → Just val) =
   let nS = s { nonceStage  = nextStage s.nonceStage
              , sendCounter = minBound
              , chunkStage  = KeySend
              } ∷ NonceState alg
       outS | stageV s.nonceStage = nS { currentV   = val }
            | otherwise           = nS { currentKey = val }
       r = bitCoerce @_ @(Unsigned (CLog 2 p)) val
   in if r /= 0 && r < natToNum @p && s.nonceStage == NonceLoopCheck
    then (initialState,
          (outputPassBy i)
          { shaInput  = i.inputMessage
          , shaOutput = None
          , isResult  = True
          }
         )
    else (outS, (outputPassBy i) { hmacInput = firstByte outS } )

  -- Waiting for HMAC to finish computing.
  s ~~> i | s.sendCounter == maxBound && lastChunk s.nonceStage == s.chunkStage =
   (s, outputPassBy i)

  -- Chunk the data into frames for HMAC.
  s ~~> i | s.chunkStage == ByteSend
         || (s.sendCounter == maxBound && lastChunk s.nonceStage /= s.chunkStage) =
   let nS = s { chunkStage = succ s.chunkStage, sendCounter = minBound }
       out = outputPassBy i 
       m = 0 :: Index (MessageDigestSize alg `Div` 8)
       hmacIn = case chunkStage nS of
        FillerSend → Middle $ error "Filler data"
        VSend      → Middle $ toV nS.currentV    !! m
        ByteSend   → extraByteFrame alg nS.nonceStage
        SeedFirst  → Middle i.inputPk
        SeedLast   → Middle $ toV nS.currentHash !! m
        _          → error "Nonce generation: should never be reached"
   in (nS, out { hmacInput = hmacIn, printPk = chunkStage nS == SeedFirst })

  s ~~> i = (nS , (outputPassBy i) { hmacInput = hmacIn })
   where
    nS = s { sendCounter = satSucc SatBound s.sendCounter }
    cP | nS.chunkStage  == lastChunk nS.nonceStage
      && nS.sendCounter == maxBound = End ()
       | otherwise                  = Middle
    hmacIn =  case nS.chunkStage of
     KeySend    → cP $ toV nS.currentKey  !! nS.sendCounter
     FillerSend → Middle $ error "Filler data"
     VSend      → cP $ toV nS.currentV    !! nS.sendCounter
     SeedFirst  → Middle i.inputPk
     SeedLast   → cP $ toV nS.currentHash !! nS.sendCounter
     _          → error "Nonce generation: should never be reached"

  output = mealy (~~>) initialState $ NonceInput
       <$> newsfeed lastRes <*> getContent shaOutput <*> pk
       <*> message          <*> hmacOutput

  (lastRes, hmacOutput)
   = hmacE alg (register NoData $ output.hmacInput)
   $ delayC $ Channel output.shaOutput
   
  shaOutput = sha alg $ register Idle output.shaInput

 in (bitCoerce <$> guardC output.isResult lastRes, output.printPk)

-- | Internal state of a round.
data SendState
 = KeySend
 | FillerSend
 | VSend
 | ByteSend
 | SeedFirst
 | SeedLast
 deriving (Eq, Show, Generic, NFDataX, Enum)

-- | The different stages of the deterministic nonce generation algorithm.
-- Apart from `NonceIdle`, they bear a one-to-one relationship with steps
-- 1.6 to 1.9, 4.2.1, 4.5, and 4.6 of the algorithm.
data NonceStage
 = InitFirst | InitSecond | InitThird | InitFourth
 | NonceLoopCheck | NonceLoopKey | NonceLoopV | NonceIdle
 deriving (Eq, Show, Enum, Generic, NFDataX)

-- | The inputs to the deterministic nonce generation's Mealy machine.
data NonceInput alg = NonceInput
 { -- | The last digest produced by HMAC.
   inputLast    ∷ Maybe (Digest alg)
   -- | The output of the SHA circuit that is either used for generating the
   --   message hash or fed to HMAC.
 , inputSha     ∷ Content (Digest alg)
   -- | The private key of the device, which comes at one byte per cycle.
 , inputPk      ∷ BitVector 8
   -- | The message to be hashed, as byte-sized frames.
 , inputMessage ∷ Frame () (Index 8) (BitVector 8)
   -- | The output from HMAC used as input for the SHA circuit.
 , inputHash    ∷ Frame () (Index 8) (BitVector 8)
 }

-- | The outputs of the deterministic nonce generation's Mealy machine.
data NonceOutput alg = NonceOutput
 { -- | A marker for termination.
   isResult  ∷ Bool
   -- | The input to the SHA circuit: it is either the output from HMAC or the
   --   input message.
 , shaInput  ∷ Frame () (Index 8) (BitVector 8)
   -- | The output of the SHA circuit, fed into HMAC.
 , shaOutput ∷ Content (Digest alg)
   -- | The input frames for HMAC, computed from the following values:
   -- * The HMAC key
   -- * The V value
   -- * The private key
   -- * The message hash
 , hmacInput ∷ Frame (Index ((BlockSize alg `Div` 8) + 1)) () (BitVector 8)
   -- | Resets the circuit outputting the private key.
 , printPk   ∷ Bool
 }

-- | The internal state of the deterministic nonce generation's Mealy machine.
data NonceState alg = NonceState
 { -- | The current step in the algorithm.
   nonceStage  ∷ NonceStage
   -- | The chunk currently being sent.
 , chunkStage  ∷ SendState
   -- | The current HMAC key.
 , currentKey  ∷ Digest alg
   -- | The current V.
 , currentV    ∷ Digest alg
   -- | The hash computed from the message.
 , currentHash ∷ Digest alg
   -- | A counter tracking how many bytes have been processed for a given
   -- chunk of data.
 , sendCounter ∷ Index (MessageDigestSize alg `Div` 8)
 } deriving Generic

instance KnownNat (MessageDigestSize alg) ⇒ NFDataX (NonceState alg)

-- | Returns the last chunk associated to a step of the algorithm.
lastChunk ∷ NonceStage → SendState
lastChunk = \case
 InitFirst      → SeedLast
 InitSecond     → VSend
 InitThird      → SeedLast
 InitFourth     → VSend
 NonceLoopCheck → VSend
 NonceLoopKey   → ByteSend
 NonceLoopV     → VSend
 NonceIdle      → error "NonceWait doesn't chunk data"

-- | Returns the extra byte frame needed by the algorithm, for the relevant
-- states.
extraByteFrame ∷ forall alg → NonceStage →
 Frame (Index ((BlockSize alg `Div` 8) + 1)) () (BitVector 8)
extraByteFrame _ = \case
 InitFirst    → Middle 0
 InitThird    → Middle 1
 NonceLoopKey → End () 0
 _            → error "These states don't use an extra byte"

-- Generic output for the Mealy machine.
outputPassBy ∷ NonceInput alg → NonceOutput alg
outputPassBy i = NonceOutput
 { isResult  = False
 , shaInput  = i.inputHash
 , shaOutput = i.inputSha
 , hmacInput = NoData
 , printPk   = False
 }

-- Returns the next stage in the algorithm.
nextStage ∷ NonceStage → NonceStage
nextStage NonceLoopV   = NonceLoopCheck
nextStage s            = succ s

-- | Is the output of the stage reused as the HMAC key or the `V` value?
stageV ∷ NonceStage → Bool
stageV  InitSecond     = True
stageV  InitFourth     = True
stageV  NonceLoopCheck = True
stageV  NonceLoopV     = True
stageV  _              = False
