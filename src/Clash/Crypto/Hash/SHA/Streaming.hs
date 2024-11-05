{-|
Module      : Clash.Crypto.Hash.SHA.Streaming
Copyright   : Copyright © 2024 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Streaming based implementation of FIPS 180-4.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.Hash.SHA.Streaming where

import Clash.Prelude
import Clash.Signal.Delayed.Extra

import Data.Constraint (Dict(..))
import Data.Constraint.Nat.Extra (DDiv)
import Data.Either (fromRight)
import Language.Haskell.Unicode (type (≤))
import Unsafe.Coerce (unsafeCoerce)

import Clash.Crypto.Hash.SHA.Specification
import Clash.Crypto.Hash.SHA.Streaming.Padding
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

-- | Streaming based implementation of the hashing algorithms defined
-- in FIPS 180-4.
hashStream ∷
  ∀ (alg ∷ SHA) (dom ∷ Domain) (n ∷ Nat) (k ∷ Nat).
  (KnownNat k, KnownSHA alg, KnownDomain dom, HiddenClockResetEnable dom) ⇒
  (KnownNat n, 1 ≤ n, n ≤ BlockSize alg, Mod (BlockSize alg) n ~ 0) ⇒
  DSignal dom k (PaddedMsgFrame n) →
  DSignal dom (k + DDiv (BlockSize alg) n) (Maybe (HashValue alg))
hashStream input
  | SHAFacts alg ← knownSHA @alg
  , Dict ← lemma₀ @(BlockSize alg) @n
  , Dict ← lemma₁ @(BitSize (MessageBlock alg)) @n
  =
  let
    -- some buffer to shift in @(BlockSize alg / n) - 1@ frames
    -- for glueing them together into a @BlockSize alg - n@ sized block
    collector ∷ DSignal dom k (Vec (DDiv (BlockSize alg) n - 1) (BitVector n))
    collector = antiDelay d1 $ delayedI @1 (repeat 0)
      $ (\x → maybe x (either (const x) (fst . shiftInAtN x . (:> Nil))))
          <$> collector
          <*> input

    -- counter that counts down on receiving some input until enough frames
    -- have been collected creating a block
    releaseCount ∷ DSignal dom k (Index (DDiv (BlockSize alg) n))
    releaseCount = antiDelay d1 $ delayedI @1 maxBound
      $ (\x → maybe x (fromRight maxBound . (satPred SatWrap x <$)))
          <$> releaseCount
          <*> input

    -- keep the data from the collector stable until the releaseCount
    -- reaches zero
    keepStable ∷ DSignal dom k Bool
    keepStable = (> 0) <$> releaseCount

    -- full message block copied over from the collector after the
    -- arrival of the @BlockSize alg / n@-th frame
    msgBlock ∷ DSignal dom (k + 1) (MessageBlock alg)
    msgBlock = delayedI @1 (repeat 0)
      $ mux keepStable (antiDelay d1 msgBlock)
      $ fmap bitCoerce
      $ (++) <$> collector
             <*> ((:> Nil) . maybe 0 (fromRight 0) <$> input)

    -- proceed with the next fold immediately after all computation is
    -- done, where we require at least a one cycle delay.
    proceedCount ∷
      DSignal dom k (Maybe (Index (k + DDiv (BlockSize alg) n)))
    proceedCount = antiDelay d1 $ delayedI @1 Nothing
      $ mux ((== 0) <$> releaseCount)
          (pure $ Just maxBound)
          (maybe Nothing (\x → if x > 0 then Just $ x - 1 else Nothing)
             <$> proceedCount
          )

    proceed ∷ DSignal dom (k + DDiv (BlockSize alg) n) Bool
    proceed = (== Just 0) <$> forward SNat proceedCount

    endOfInputReceived ∷ DSignal dom k Bool
    endOfInputReceived = antiDelay d1 $ delayedI @1 False
      $    ((== (Just $ Left ())) <$> input)
      .||. (endOfInputReceived .&&. ((/= Just 0) <$> proceedCount))

    endOfMessage ∷ DSignal dom (k + DDiv (BlockSize alg) n) Bool
    endOfMessage = proceed .&&. forward SNat endOfInputReceived

    rstF ∷ Reset dom
    rstF = unsafeFromActiveHigh
         $ toSignal
         $ delayedI @1 False endOfMessage

    -- apply the for loop "For i=1 to N:"
    hashValue ∷ DSignal dom (k + DDiv (BlockSize alg) n) (HashValue alg)
    hashValue = withReset rstF $
      dsFold
        (_H⁰ alg)
        (computeBlock @alg @(DDiv (BlockSize alg) n - 1) SNat)
        $ mux (delayedI @1 False ((== 0) <$> releaseCount))
            (Just <$> msgBlock)
            (pure Nothing)
  in
    mux endOfMessage
      (Just <$> hashValue)
      (pure Nothing)

 where
  lemma₀ ∷
    ∀ (a ∷ Nat) (b ∷ Nat).
    (1 ≤ a, 1 ≤ b, Mod a b ~ 0) ⇒
    Dict (1 ≤ Div a b)
  lemma₀ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  lemma₁ ∷
    ∀ (a ∷ Nat) (b ∷ Nat).
    (1 ≤ Div a b, Mod a b ~ 0) ⇒
    Dict (((Div a b - 1) + 1) * b ~ a)
  lemma₁ = unsafeCoerce (Dict ∷ Dict (0 ~ 0))
