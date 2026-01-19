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

module Clash.Crypto.ECDSA.DeterministicNonce
  ( deriveNonce
  , genericRound
  , chunkContent
  , ChunkPosition (..)
  , SendStateI (..)
  ) where

import Clash.Prelude
import Clash.Signal.Channel
import Clash.Signal.DataStream
import Clash.Signal.Extra (apWhen)

import Data.Constraint.Nat.Extra (CancelMultiple)
import GHC.TypeNats.Proof (Rewrite(..), using)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Hash.SHA
import qualified Clash.Crypto.Calculator.Modulo as M

import Clash.Crypto.MAC.HMAC
import Data.Functor ((<&>))


-- | An implementation of the deterministic nonce generation for ECDSA found
-- in Appendix A.3.3 of FIPS 186-5. The outputted number is returned *before*
-- computing its power since it makes sharing resources easier in the context
-- of a circuit.
deriveNonce ∷
  ∀ (dom ∷ Domain). (HiddenClockResetEnable dom) ⇒
  ∀ (p ∷ Nat)  → (KnownNat p, 1 ≤ p) ⇒
  ∀ (alg ∷ SHA) → (KnownSHA alg, KnownNat (MessageDigestSize alg),
    CLog 2 p ~ MessageDigestSize alg, 1 ≤ MessageDigestSize alg `Div` 8) ⇒
  (8 ≤ BlockSize alg, Mod (BlockSize alg) 8 ~ 0) ⇒
  DataStream dom () (Index 8) (BitVector 8) →
  -- ^ message
  Channel dom (Digest alg) →
  -- ^ private key
  Channel dom (M.Mod p)
  -- ^ k, the nonce to be multiplied afterwards (→ k ^ 16)
deriveNonce p alg message pk
 | SHAFacts ← knownSHA alg
 , Rewrite  ← using @(CancelMultiple (MessageDigestSize alg) 8)
 = bitCoerce <$> let
  roundReset = (/=) <$> stage <*> register NonceWait stage
  (stage, byte, bfActive)
   = unbundle $ moore (~~>) compute NonceWait
   $ bundle (lastResult.hasUpdates, shaOutput.hasUpdates, isResult)
  NonceWait    ~~> (_   , True, _    ) = InitFirst
  InitFirst    ~~> (True, _   , _    ) = InitSecond
  InitSecond   ~~> (True, _   , _    ) = InitThird
  InitThird    ~~> (True, _   , _    ) = InitFourth
  InitFourth   ~~> (True, _   , _    ) = NonceLoopLen
  NonceLoopLen ~~> (True, _   , False) = NonceLoopKey
  NonceLoopLen ~~> (True, _   , True ) = NonceWait
  NonceLoopKey ~~> (True, _   , _    ) = NonceLoopV
  NonceLoopV   ~~> (True, _   , _    ) = NonceLoopLen
  s            ~~> _                   = s
  -- We pack only three values here because packing one more makes the circuit
  -- take more space on the board.
  compute s = (s, byteC s, bfActiveC s)
  byteC = \case
    InitFirst → Middle 0
    InitThird → Middle 1
    _         → End () 0
  bfActiveC = \case
    InitFirst    → True
    InitThird    → True
    NonceLoopKey → True
    _            → False
  lastChunk = stage <&> \case
    InitFirst    → SeedLast
    InitThird    → SeedLast
    NonceLoopKey → ByteSend
    _            → VSend
  -- Initial values
  initialV, initialKey ∷ Digest alg
  initialV   = bitCoerce $ repeat (0x01 ∷ BitVector 8)
  initialKey = 0
  -- TODO: Find a way to nicely rewrite these muxes
  v   = muxC ((== InitFirst) <$> stage) (pure initialV)
      $ muxC ((\s → s == InitSecond || s == InitFourth || s == NonceLoopLen ||
                    s == NonceLoopV) <$> stage .&&. lastResult.hasUpdates)
        lastResult
      $ delayC v
  key = muxC ((\s → s == InitFirst || s == InitThird ||
                    s == NonceLoopKey) <$> stage .&&. lastResult.hasUpdates)
        lastResult
      $ muxC ((== InitFirst) <$> stage) (pure initialKey)
      $ delayC key
  (lastResult, hmacOutput) = hmacE alg roundOutput
   $ muxC ((== NonceWait) <$> stage) (Channel $ pure None) shaOutput
  roundOutput =
   genericRound alg bfActive byte lastChunk roundReset key v pk messageHash
  shaOutput = delayC
            $ sha alg
            $ mux ((== NonceWait) <$> stage) message hmacOutput
  messageHash = muxC ((== NonceWait) <$> stage .&&. shaOutput.hasUpdates)
                     shaOutput $ delayC messageHash
  modResult = bitCoerce @_ @(Unsigned (CLog 2 p)) <$> lastResult
  isResult  = maybe False (\m → m /= 0 || m < natToNum @p)
          <$> content modResult
 in guardC
  ((== NonceLoopLen) <$> register NonceWait stage .&&. isResult) modResult

-- | An implementation of a generic round for deterministic nonce generation.
-- The three different types of rounds are parametrized over three specific
-- values, which are enough to represent all rounds in the algorithm:
-- * An additional byte frame
-- * A toggle for this byte frame
-- * The type of data to be sent last
genericRound ∷ forall dom.
  forall alg → (KnownSHA alg, HiddenClockResetEnable dom,
   BlockSize alg `Mod` 8 ~ 0, 8 ≤ BlockSize alg,
   1 ≤ MessageDigestSize alg `Div` 8) ⇒
  Signal dom Bool →
  -- ^ is there a single-byte frame?
  Signal dom (Frame (Index ((BlockSize alg `Div` 8) + 1)) () (BitVector 8)) →
  -- ^ the single-byte frame
  Signal dom SendStateI →
  -- ^ the state of the last chunk
  Signal dom Bool →
  -- ^ reset signal
  Channel dom (Digest alg) →
  -- ^ the HMAC key
  Channel dom (Digest alg) →
  -- ^ the V value
  Channel dom (Digest alg) →
  -- ^ first part of the seed (private key)
  Channel dom (Digest alg) →
  -- ^ last part of the seed (message hash)
  DataStream dom (Index ((BlockSize alg `Div` 8) + 1)) () (BitVector 8)
  -- ^ the resulting stream to be fed to HMAC
genericRound alg bfActive byteFrame lastChunk rst keyC vC seed1 seed2
 | SHAFacts ← knownSHA alg
 , Rewrite  ← using @(CancelMultiple (MessageDigestSize alg) 8) =
 let
  stage = moore (~~>) id RoundIdle $ bundle (rst, chunkerDone, lastChunk)
  _                     ~~> (True, _   , _ ) = WaitNext KeySend
  Processing s          ~~> (_   , True, lc) | s == lc = RoundIdle
  Processing KeySend    ~~> (_   , True, _ ) = WaitNext FillerSend
  Processing FillerSend ~~> (_   , True, _ ) = WaitNext VSend
  Processing VSend      ~~> (_   , True, _ ) = Processing ByteSend
  Processing ByteSend   ~~> (_   , True, _ ) = WaitNext SeedFirst
  Processing SeedFirst  ~~> (_   , True, _ ) = WaitNext SeedLast
  Processing SeedLast   ~~> (_   , True, _ ) = RoundIdle
  WaitNext s            ~~> (_   , True, _ ) = WaitNext s
  WaitNext s            ~~> _                = Processing s
  s                     ~~> _                = s
  chunkType = do
     curStage ← stage
     chunk    ← lastChunk
     pure $ case curStage of
       (isState KeySend → True) → FirstChunk
       (isState chunk   → True) → LastChunk
       _                        → MiddleChunk
  dataToChunk
   = muxCFresh (isState KeySend    <$> stage) keyC
   $ muxCFresh (isState FillerSend <$> stage) (pure undefined)
   $ muxCFresh (isState VSend      <$> stage) vC
   $ muxCFresh (isState SeedFirst  <$> stage) seed1
   $ muxCFresh (isState SeedLast   <$> stage) seed2
   $ Channel $ pure None
  (chunker, chunkerDone) = chunkContent alg dataToChunk chunkType
 in mux ((== RoundIdle)           <$> stage)               (pure Idle)
  $ mux ((== Processing ByteSend) <$> stage .&&. bfActive) byteFrame chunker

-- | The different stages of the deterministic nonce generation algorithm.
data NonceStage
 = InitFirst | InitSecond | InitThird | InitFourth
 | NonceLoopLen | NonceLoopKey | NonceLoopV | NonceWait
 deriving (Eq, Generic, NFDataX)

-- | Internal state of a round.
data SendStateI
 = KeySend
 | FillerSend
 | VSend
 | ByteSend
 | SeedFirst
 | SeedLast
 deriving (Eq, Show, Generic, NFDataX, Enum)

-- | Actual state of a round.
data SendStateE
 = WaitNext SendStateI
 | Processing SendStateI
 | RoundIdle
 deriving (Eq, Show, Generic, NFDataX)

-- | A handy comparison operator.
isState ∷ SendStateI → SendStateE → Bool
isState s (Processing t) = s == t
isState s (WaitNext   t) = s == t
isState _ _              = False

-- | A small helper function that makes a mux Fresh when the condition updates.
muxCFresh ∷ ∀ a dom. (HiddenClockResetEnable dom, KnownDomain dom) ⇒
 Signal dom Bool → Channel dom a → Channel dom a → Channel dom a
muxCFresh b x y = muxC b (freshen $ oldify x) (freshen y)
 where
  changed = xor <$> b <*> register False b
  freshen = Channel . apWhen changed (Fresh id <*>) . getContent
  oldify  = Channel . fmap (\case
                            Fresh x' → Old x'
                            s        → s     ) . getContent

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
  stage :: Signal dom (Index (MessageDigestSize alg `Div` 8 + 1))
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
  makeVec ∷ Maybe (BitVector (MessageDigestSize alg)) →
       Maybe (Vec (MessageDigestSize alg `Div` 8) (BitVector 8))
  makeVec = fmap bitCoerce
  frame (cont, typ, curStage)
   = maybe NoData (op curStage typ) ((!! curStage) <$> makeVec cont)
 in
  (frame <$> bundle (content contC, chunkType, stage), (== maxBound) <$> stage)
