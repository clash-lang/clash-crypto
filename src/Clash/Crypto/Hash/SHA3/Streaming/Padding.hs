{-|
Module      : Clash.Crypto.Hash.SHA3.Streaming.Padding
Copyright   : Copyright © 2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Streaming based padding implementation of FIPS 202.
-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiWayIf #-}

module Clash.Crypto.Hash.SHA3.Streaming.Padding (pad) where

import Clash.Prelude
import Clash.Sized.Internal.BitVector

import Language.Haskell.Unicode (type (≤))
import GHC.TypeNats.Proof (type (<))

import Data.Constraint.Nat.Extra (DDiv)
import Clash.Signal.DataStream (DataStream, Frame(..))
import Clash.Crypto.Hash.SHA3.Types (SHA3, AlgRate)
import Clash.Crypto.Hash.SHA3.Properties
    (KnownSHA3(..), SHA3Facts(SHA3Facts), SuffixConstants(..))

-- | The data type of the state of the controller of padding circuit.
type CollectAndPadState ∷ Nat → SHA3 → Type
data CollectAndPadState n alg =
    SIdle
  -- ^ Idle state. Waiting for input DataStream.
  | Reading
  -- ^ Reading state. Collecting input frames.
    (Index (DDiv (AlgRate alg) n))
    -- ^ Input frames that have been ingested.
  | EmitEndFrame
  -- ^ In this state the whole message has been read.
   (Index (DDiv (AlgRate alg) n))
   -- ^ Number of frames that have been output.
   (TerminationState alg)
  -- ^ The state of the termination.
    deriving (Generic, NFDataX)

-- | A data type to hold the progress of the padding appended in the last output frame.
type TerminationState ∷ SHA3 → Type
data TerminationState alg =
    OnlySuffixAndFirstHighTerminated
  -- ^ Only the suffix and the first high bit of the
  -- padding has been added to the last frame.
  | OnlySuffixTerminated
  -- ^ Only the suffix has been added to the last frame and no bits from the padding.
  | SuffixNotTerminated (Index (SuffixLen alg))
  -- ^ How many bits of the suffix are appended to the last frame.
  deriving (Show, Generic, NFDataX)

-- | A circuit implementation that:
--
-- * Ingests input frames of size n and emits frames of size n.
-- * Pads the total message so that the final length is divisable by @AlgRate alg@
-- using the pad10*1 algorithm.
-- It will have output the whole padded message in at most + 1 cycles after
-- reading End.
pad ∷
  ∀ (n ∷ Nat) (dom ∷ Domain).
  (KnownNat n, HiddenClockResetEnable dom, 1 ≤ n) ⇒
  ∀ (alg ∷ SHA3) → KnownSHA3 alg ⇒
  (AlgRate alg `Mod` n ~ 0, SuffixLen alg < n) ⇒
  DataStream dom () (Index n) (BitVector n) →
  DataStream dom () () (BitVector n)
pad alg input
  | SHA3Facts ← knownSHA3 alg =
  let
    transfer ∷
      CollectAndPadState n alg →
      Frame () (Index n) (BitVector n) →
      (CollectAndPadState n alg, Frame () () (BitVector n))
    transfer state frame = case (state, frame) of
      (SIdle, Idle)             → (SIdle, Idle)
      (SIdle, Start () f)       → (Reading 1, Start () f)
      (SIdle, End r f)          →
        let (term, isLast) = controlSignalsOnEnd alg 0 r
            outFrame = constructLast alg (isLast, r) f
        in if isLast
           then (SIdle, End () outFrame)
           else (EmitEndFrame 1 term, Start () outFrame)
      (Reading n, Middle f)     → (Reading (satSucc SatWrap n), Middle f)
      (Reading n, Stretch)      → (Reading n, Stretch)
      (Reading n, End r f)      →
        let (term, isLast) = controlSignalsOnEnd alg n r
            outFrame = constructLast alg (isLast, r) f
        in if isLast
           then (SIdle, End () outFrame)
           else (EmitEndFrame (satSucc SatWrap n) term, Middle outFrame)
      (EmitEndFrame fc term, _) →
          let (newterm, isLast) = controlSignalsOnTermination n alg fc term
              outFrame = constructExtra alg term isLast
          in if isLast
           then (SIdle, End () outFrame)
           else (EmitEndFrame (satSucc SatError fc) newterm, Middle outFrame)
      _                         → errorX "unexpected input"

  in mealy transfer SIdle input

controlSignalsOnEnd ∷
  ∀ (n ∷ Nat). (KnownNat n, 1 ≤ n) ⇒
  ∀ (alg ∷ SHA3) → KnownSHA3 alg ⇒
  (AlgRate alg `Mod` n ~ 0, SuffixLen alg < n) ⇒
  Index (DDiv (AlgRate alg) n) →
  Index n →
  (TerminationState alg, Bool)
controlSignalsOnEnd alg fc remainder
  | SHA3Facts ← knownSHA3 alg =
  let
    sfxLen = natToNum @(SuffixLen alg)
  in if | remainder < sfxLen      →
          (SuffixNotTerminated (resize remainder), False)
        | remainder == sfxLen     →
          (OnlySuffixTerminated, False)
        | remainder == sfxLen + 1 →
          (OnlySuffixAndFirstHighTerminated, False)
        | otherwise               →
          (OnlySuffixAndFirstHighTerminated, maxBound == fc)

controlSignalsOnTermination ∷
  ∀ (n ∷ Nat) → (KnownNat n, 1 ≤ n) ⇒
  ∀ (alg ∷ SHA3) → KnownSHA3 alg ⇒
  (AlgRate alg `Mod` n ~ 0) ⇒
  Index (DDiv (AlgRate alg) n) →
  TerminationState alg →
  (TerminationState alg, Bool)
controlSignalsOnTermination n alg fc term
  | SHA3Facts ← knownSHA3 alg =
  let
    sfxLen = natToNum @(SuffixLen alg)
    nn = natToNum @n
  in case term of
    SuffixNotTerminated emittedSuffix →
      if | nn < sfxLen - fromEnum emittedSuffix           →
          (SuffixNotTerminated (natToNum @n), False)
         | natToNum @n == sfxLen - fromEnum emittedSuffix →
          (OnlySuffixTerminated, False)
         | nn == sfxLen - fromEnum emittedSuffix + 1      →
          (OnlySuffixAndFirstHighTerminated, False)
         | otherwise                                      →
          (OnlySuffixAndFirstHighTerminated, maxBound == fc)
    OnlySuffixTerminated              →
      if nn == 1
      then (OnlySuffixAndFirstHighTerminated, False)
      else (OnlySuffixAndFirstHighTerminated, fc == maxBound)
    OnlySuffixAndFirstHighTerminated  →
      (OnlySuffixAndFirstHighTerminated, fc == maxBound)

-- | A circuit to compute the last output frame containing data.
-- It adds the suffix and correct ammount of padding to a
-- candidate output frame.
constructLast ∷
  ∀ (n ∷ Nat). (KnownNat n, 1 ≤ n) ⇒
  ∀ (alg ∷ SHA3) → KnownSHA3 alg ⇒
  (Bool, Index n) →
  BitVector n →
  BitVector n
constructLast alg (setLeast, remainder) frame
  | SHA3Facts ← knownSHA3 alg =
  let
    remn = fromEnum remainder
    noTrailing = shiftR frame remn
    sfxd = noTrailing
      ++# suffix alg
      ++# (pack high ∷ BitVector 1)
    zfxdZeros = shiftL sfxd remn
    (res, _) = split zfxdZeros
  in if setLeast then setLSB res else res

-- | A circuit to compute the extra end output frame.
-- This is needed if the message could not be padded in a single frame,
-- so we need an overflow End frame.
constructExtra ∷
  ∀ (n ∷ Nat). KnownNat n ⇒
  ∀ (alg ∷ SHA3) →
  (KnownNat (AlgRate alg), SuffixConstants alg, KnownNat (SuffixLen alg)) ⇒
  TerminationState alg →
  Bool →
  BitVector n
constructExtra alg termination isLast =
  let shiftN = case termination of
        SuffixNotTerminated d            → fromEnum d
        OnlySuffixTerminated             → natToNum @(SuffixLen alg)
        OnlySuffixAndFirstHighTerminated → natToNum @(SuffixLen alg) + 1
      shifted = shiftL# res shiftN
  in if isLast then setLSB shifted else shifted
 where
  sfxPad =     suffix alg
           ++# (oneBits ∷ BitVector 1)
           ++# zeroBits :: BitVector (SuffixLen alg + 1 + n)
  (res, _) = split# sfxPad

setLSB ∷
  ∀ (n ∷ Nat). KnownNat n ⇒
  BitVector n →
  BitVector n
setLSB vec = replaceBit# vec (0 ∷ Int) high
