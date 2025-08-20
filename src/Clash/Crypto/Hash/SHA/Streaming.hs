{-|
Module      : Clash.Crypto.Hash.SHA.Streaming
Copyright   : Copyright © 2024-2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Streaming based implementation of FIPS 180-4.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.Hash.SHA.Streaming
  ( hashStream
  , computeBlock
  ) where

import Clash.Prelude
import Clash.Signal.Channel
import Clash.Signal.DataStream
import Clash.Signal.Delayed.Extra
import Clash.Signal.Extra (apWhen)

import Data.Constraint.Nat.Extra (DDiv, CancelMultiple, KeepsPositiveIfMultiple)
import GHC.TypeNats.Proof (Rewrite(..), using)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Hash.SHA.Specification
import Clash.Crypto.Hash.SHA.Streaming.Stages

-- | Perform the steps 1 to 4 for one iteration of the loop.
computeBlock ∷
  ∀ (alg ∷ SHA). KnownSHA alg ⇒
  ∀ stages. SNat stages →
  ∀ dom n. (KnownDomain dom, HiddenClockResetEnable dom) ⇒
  DSignal dom n (Maybe (MessageBlock alg, HashValue alg)) →
  DSignal dom (n + stages) (HashValue alg)
computeBlock stages@SNat input
  | SHAFacts alg ← knownSHA @alg
  = let hvs = (`maybe` snd)
          <$> antiDelay d1 (delayedI @1 undefined hvs)
          <*> input
     in ((zipWith (+) <$> forward stages hvs) <*>)
      $ snd <$> mealyStages stages (slidingWindowCycle alg) input

-- | Streaming based implementation for the hashing algorithms defined
-- in FIPS 180-4.
hashStream ∷
  ∀ (alg ∷ SHA) (dom ∷ Domain) (n ∷ Nat).
  (KnownSHA alg, KnownDomain dom, HiddenClockResetEnable dom) ⇒
  (KnownNat n, 1 ≤ n, n ≤ BlockSize alg, Mod (BlockSize alg) n ~ 0) ⇒
  DataStream dom () () (BitVector n) →
  Channel dom (HashValue alg)
hashStream input
  | SHAFacts alg ← knownSHA @alg
  , Rewrite ← using @(KeepsPositiveIfMultiple (BlockSize alg) n)
  , let lemma ∷
          ∀ (m ∷ Nat).
          (1 ≤ Div m n, Mod m n ~ 0) ⇒
          Rewrite (((Div m n - 1) + 1) * n ~ m)
        lemma | Rewrite ← using @(CancelMultiple m n) = Rewrite
  , Rewrite ← lemma @(BitSize (MessageBlock alg))
  =
  let
    -- some buffer to shift in @(BlockSize alg / n) - 1@ frames
    -- for glueing them together into a @BlockSize alg - n@ sized block
    collector ∷ Signal dom (Vec (DDiv (BlockSize alg) n - 1) (BitVector n))
    collector = register (repeat 0)
      $ liftA2 (\x → mayD x (x <<+)) collector input

    -- the point in time at which the last frame of the incoming
    -- message block has arrived
    blockComplete ∷ Signal dom Bool
    blockComplete = blockCount .== 0 .&&. input.hasData
     where
       blockCount = register (maxBound ∷ Index (DDiv (BlockSize alg) n))
         $ liftA2 (\x → mayD x (const $ satPred SatWrap x)) blockCount input

    -- full message block copied over from the collector after the
    -- arrival of the @BlockSize alg / n@-th frame
    msgBlock ∷ DSignal dom 1 (MessageBlock alg)
    msgBlock = delayedI @1 (repeat 0)
      $ fromSignal
      $ mux (not <$> blockComplete) (toSignal msgBlock)
      $ fmap bitCoerce
      $ liftA2 (++) collector
      $ (:> Nil) . mayD 0 id <$> input

    -- proceed with the next fold immediately after all computation is
    -- done, where we require at least a one cycle delay
    proceed ∷ Signal dom Bool
    proceed = stepCount .== Just 0
     where
      stepCount = register (Nothing ∷ Maybe (Index (DDiv (BlockSize alg) n)))
        $ apWhen blockComplete (const $ pure maxBound)
        $ apWhen (maybe False (> 0) <$> stepCount) (satPred SatBound <$>)
          stepCount

    -- marks the time after the input has been received and
    -- calculations are still running
    afterInput ∷ Signal dom Bool
    afterInput = register False
      $ delay False input.atEndFrame .||.
        afterInput .&&. not <$> proceed

    -- apply the for loop "For i=1 to N:"
    hashValue ∷ Signal dom (HashValue alg)
    hashValue = toSignal
      $ dsFold (_H⁰ alg) (fromSignal input.atStartFrame)
          (computeBlock @alg @(DDiv (BlockSize alg) n - 1) SNat)
      $ mux (delayedI @1 False $ fromSignal blockComplete)
          (Just <$> msgBlock)
          (pure Nothing)
  in
    channel hashValue
      $ mux input.atStartFrame        (pure Clear)
      $ mux (proceed .&&. afterInput) (pure Release)
                                      (pure Keep)
