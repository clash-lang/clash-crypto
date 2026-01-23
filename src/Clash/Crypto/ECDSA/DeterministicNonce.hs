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

module Clash.Crypto.ECDSA.DeterministicNonce
  ( deriveNonce
  , chunkContent
  , ChunkPosition (..)
  , SendState (..)
  ) where

import Clash.Prelude
import Clash.Signal.Channel
import Clash.Signal.DataStream

import Data.Constraint.Nat.Extra (CancelMultiple)
import GHC.TypeNats.Proof (Rewrite(..), using)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Hash.SHA
import qualified Clash.Crypto.Calculator.Modulo as M

import Clash.Crypto.MAC.HMAC
import Clash.Class.Counter (countSucc)
import Clash.Debug (traceShowId)

-- | The different stages of the deterministic nonce generation algorithm.
data NonceStage
 = InitFirst | InitSecond | InitThird | InitFourth
 | NonceLoopLen | NonceLoopKey | NonceLoopV | NonceWait
 deriving (Eq, Show, Enum, Generic, NFDataX)

data NonceInput alg = NonceInput
 { inputLast    ∷ Maybe (Digest alg)
 , inputSha     ∷ Content (Digest alg)
 , inputPk      ∷ BitVector 8
 , inputMessage ∷ Frame () (Index 8) (BitVector 8)
 , inputHash    ∷ Frame () (Index 8) (BitVector 8)
 , inputChunk   ∷ Frame (Index ((BlockSize alg `Div` 8) + 1)) () (BitVector 8)
 , chunkerDone  ∷ Bool
 }

data NonceOutput alg = NonceOutput
 { isResult  ∷ Bool
 , toChunk   ∷ Maybe (Digest alg)
 , shaInput  ∷ Frame () (Index 8) (BitVector 8)
 , shaOutput ∷ Content (Digest alg)
 , hmacInput ∷ Frame (Index ((BlockSize alg `Div` 8) + 1)) () (BitVector 8)
 , chunkPos  ∷ ChunkPosition
 , printPk   ∷ Bool
 }

data NonceState alg = NonceState
 { nonceStage  ∷ NonceStage
 , chunkStage  ∷ SendState
 , currentKey  ∷ Digest alg
 , currentV    ∷ Digest alg
 , currentHash ∷ Digest alg
 , sendCounter ∷ Index (MessageDigestSize alg `Div` 8)
 } deriving Generic

instance KnownNat (MessageDigestSize alg) ⇒ NFDataX (NonceState alg)

lastChunk ∷ NonceStage → SendState
lastChunk = \case
 InitFirst    → SeedLast
 InitSecond   → VSend
 InitThird    → SeedLast
 InitFourth   → VSend
 NonceLoopLen → VSend
 NonceLoopKey → ByteSend
 NonceLoopV   → VSend
 NonceWait    → error "NonceWait doesn't chunk data"

extraByteFrame ∷ forall alg → NonceStage →
 Frame (Index ((BlockSize alg `Div` 8) + 1)) () (BitVector 8)
extraByteFrame _ = \case
 InitFirst    → Middle 0
 InitThird    → Middle 1
 NonceLoopKey → End () 0
 _            → error "These states don't use an extra byte"

-- Output for most of the states
outputPassBy ∷ NonceInput alg → NonceOutput alg
outputPassBy i = NonceOutput
 { isResult  = False
 , toChunk   = Nothing
 , shaInput  = i.inputHash
 , shaOutput = i.inputSha
 , hmacInput = i.inputChunk
 , chunkPos  = FirstChunk
 , printPk   = False
 }

nextStage ∷ NonceStage → NonceStage
nextStage NonceLoopV   = NonceLoopLen
nextStage s            = succ s

stageV ∷ NonceStage → Bool
stageV    InitSecond   = True
stageV    InitFourth   = True
stageV    NonceLoopLen = True
stageV    NonceLoopV   = True
stageV    _            = False

-- | An implementation of the deterministic nonce generation for ECDSA found
-- in Appendix A.3.3 of FIPS 186-5. The outputted number is returned *before*
-- computing its power since it makes sharing resources easier in the context
-- of a circuit.

deriveNonce ∷
  ∀ (dom ∷ Domain). (HiddenClockResetEnable dom) ⇒
  ∀ (p ∷ Nat)  → (KnownNat p, 1 ≤ p) ⇒
  ∀ (alg ∷ SHA) →
  (KnownSHA alg, CLog 2 p ~ MessageDigestSize alg,
   1 ≤ MessageDigestSize alg `Div` 8) ⇒
  (8 ≤ BlockSize alg, Mod (BlockSize alg) 8 ~ 0) ⇒
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
   { nonceStage  = NonceWait
   , chunkStage  = KeySend
   , currentV    = bitCoerce $ repeat (0x01 ∷ BitVector 8)
   , currentKey  = 0
   , currentHash = error "Initial hash in not defined nor used"
   , sendCounter = minBound
   }

  (~~>) ∷ NonceState alg → NonceInput alg → (NonceState alg, NonceOutput alg)
  -- Start the generation if a new message has been processed.
  s@(nonceStage → NonceWait) ~~> i =
   let out = (outputPassBy i) { shaOutput = None } ∷ NonceOutput alg in
   case i.inputSha of
    Fresh h → (nS, out { toChunk = Just nS.currentKey })
     where nS = s { nonceStage  = InitFirst
                  , chunkStage  = KeySend
                  , currentHash = h
                  }
    _ → (s, out { shaInput  = i.inputMessage })

  -- Process data from HMAC.
  s ~~> i@(inputLast → Just val) =
   let nS = s { nonceStage = nextStage s.nonceStage
              , chunkStage = KeySend } ∷ NonceState alg
       outS | stageV s.nonceStage = nS { currentV   = val }
            | otherwise           = nS { currentKey = val }
       r = bitCoerce @_ @(Unsigned (CLog 2 p)) val
   in if r /= 0 && r < natToNum @p && s.nonceStage == NonceLoopLen
    then (initialState,
          (outputPassBy i)
          { shaInput  = i.inputMessage
          , shaOutput = None
          , isResult  = True
          }
         )
    else (outS, (outputPassBy i) { toChunk = Just outS.currentKey } )

  -- Chunk the data
  s ~~> i | s.chunkStage == ByteSend
         || (s.sendCounter == maxBound && s.chunkStage == SeedFirst)
         || (i.chunkerDone && lastChunk s.nonceStage /= s.chunkStage) =
   let cP = if nS.chunkStage == lastChunk nS.nonceStage
            then LastChunk else MiddleChunk
       nS = s { chunkStage = succ s.chunkStage, sendCounter = minBound }
       out = (outputPassBy i) { chunkPos = cP } ∷ NonceOutput alg
       outFinal =
        case chunkStage nS of
         VSend      → out { toChunk   = Just nS.currentV }
         FillerSend → out { toChunk   = Just $ error "Filler data" }
         ByteSend   → out { hmacInput = extraByteFrame alg nS.nonceStage }
         SeedFirst  → out { hmacInput = Middle i.inputPk, printPk = True }
         SeedLast   → out { toChunk   = Just nS.currentHash }
         _          → error "Nonce generation: should never be reached"
   in (nS, outFinal)

  -- Wait for the data to be chunked or for the last chunk to be processed.
  s ~~> i = ( s { sendCounter = countSucc s.sendCounter }
            , case s.chunkStage of
               SeedFirst -> (outputPassBy i) { hmacInput = Middle i.inputPk }
               _         -> (outputPassBy i) { chunkPos  = cP }
            )
   where
    cP | s.chunkStage == lastChunk s.nonceStage = LastChunk
       | s.chunkStage == KeySend                = FirstChunk
       | otherwise                              = MiddleChunk

  output = mealy (~~>) initialState $ NonceInput
       <$> newsfeed lastRes <*> getContent shaOutput <*> pk
       <*> message          <*> hmacOutput
       <*> chunked          <*> cDone

  (chunked, cDone)
   = chunkContent alg (cachedFromMaybe $ register Nothing output.toChunk)
   $ register FirstChunk output.chunkPos

  (lastRes, hmacOutput)
   = hmacE alg output.hmacInput
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

-- | The position of the chunk in the stream.
data ChunkPosition = FirstChunk | MiddleChunk | LastChunk
 deriving (Generic, NFDataX)

-- | Chunks the provided `BitVector` into smaller pieces, taking account of
-- the chunk's position in the stream.
chunkContent ∷ forall dom. HiddenClockResetEnable dom ⇒
  ∀ (alg ∷ SHA) → (KnownSHA alg, KnownNat (MessageDigestSize alg),
   KnownNat (BlockSize alg), 1 ≤ MessageDigestSize alg `Div` 8) ⇒
  Channel dom (BitVector (MessageDigestSize alg)) →
  -- ^ content to chunk
  Signal dom ChunkPosition →
  -- ^ position of the chunk in the stream
  ( DataStream dom (Index ((BlockSize alg `Div` 8) + 1)) () (BitVector 8)
  -- ^ output stream
  , Signal dom Bool
  -- ^ return signal (True when finished chunking)
  )
chunkContent alg contC chunkType
 | SHAFacts ← knownSHA alg
 , Rewrite  ← using @(CancelMultiple (MessageDigestSize alg) 8) =
 let
  stage ∷ Signal dom (Index (MessageDigestSize alg `Div` 8 + 1))
  stage = register maxBound
        $ mux contC.hasUpdates (pure 0)
        $ mux contC.isNonEmpty (satSucc SatBound <$> stage) stage
  opFirst curStage =
   case curStage of
    0 → Start $ natToNum @(MessageDigestSize alg `Div` 8)
    _ → Middle
  opLast curStage = if curStage == maxBound - 1 then End () else Middle
  op curStage typ = if curStage == maxBound then const NoData else
   case typ of
    FirstChunk  → opFirst curStage
    MiddleChunk → Middle
    LastChunk   → opLast curStage
  frame cont typ curStage
   = maybe NoData (op curStage typ) $ ((!! curStage) . bitCoerce) <$> cont
  done =
   (== maxBound) <$> stage .&&. register True ((/= maxBound) <$> stage)
 in
  (frame <$> content contC <*> chunkType <*> stage, done)
