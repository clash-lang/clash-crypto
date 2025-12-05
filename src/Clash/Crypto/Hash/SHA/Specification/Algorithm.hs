{-|
Module      : Clash.Crypto.Hash.SHA.Specification.Algorithm
Copyright   : Copyright © 2024 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Algorithmic reference implementation of FIPS 180-4 using a purely
functional description.
-}

{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}

module Clash.Crypto.Hash.SHA.Specification.Algorithm
  ( hash
  , computeCycles
  , toDigest
  ) where

import Clash.Prelude

import Data.Function ((&))
import GHC.TypeNats.Proof (Rewrite(..), using)
import Language.Haskell.Unicode (type (≤))
import Unsafe.Coerce (unsafeCoerce)

import Clash.Crypto.Hash.SHA.Specification.Types
import Clash.Crypto.Hash.SHA.Specification.Definitions
import Clash.Crypto.Hash.SHA.Specification.Properties
import Data.Constraint.Nat.Extra
  ( ModBound, TimesMonotoneRight, LeTrans, CancelMultiple, CancelFactor
  , CondMonotoneGE
  )

-- | Purely functional reference implementation of the hashing
-- algorithms defined in FIPS 180-4.
hash ∷
  ∀ (ℓ ∷ Nat). KnownNat ℓ ⇒
  ∀ (alg ∷ SHA) → KnownSHA alg ⇒
  Message ℓ →
  -- ^ input message
  BitVector (MessageDigestSize alg)
  -- ^ resulting message digest
hash alg msg
  | SHAFacts ← knownSHA alg
  , Rewrite ← using @(ModBound ℓ (BlockSize alg))
  , Rewrite ← using @(CondMonotoneGE 1 1 2
      (1 + SizeBits alg <=? BlockSize alg - ℓ `Mod` BlockSize alg))
  , Rewrite ← using
      @( TimesMonotoneRight
           (RequiredBlocks alg ℓ)
           (BlockSize alg)
           (BlockSize alg)
       )
  , Rewrite ← using
      @( LeTrans
           (ℓ `Mod` BlockSize alg)
           (BlockSize alg)
           (RequiredBlocks alg ℓ * BlockSize alg)
       )
  , Rewrite ← lemma₀ alg ℓ
  , Rewrite ← lemma₁ alg ℓ
  , Rewrite ← lemma₂ alg ℓ
  , Rewrite ← lemma₃ alg ℓ
  , Rewrite ← using @(CancelMultiple (PaddedMsgBits alg ℓ) (WordSize alg))
  , Rewrite ← using
      @( CancelFactor
           (PaddedMsgBits alg ℓ)
           (WordSize alg)
           MessageBlockWords
       )
  = let
      -- pad the message according to description of Section 5.1
      paddedMessage ∷ Message (PaddedMsgBits alg ℓ)
      paddedMessage =
            msg
        ++# (1 ∷ BitVector 1)
        ++# (0 ∷ BitVector (PaddingZeros alg ℓ))
        ++# pack (natToNum @ℓ @(Unsigned (SizeBits alg)))

      -- split the padded message into a words
      pmAsVWords ∷
        Vec (PaddedMsgBits alg ℓ `Div` WordSize alg) (SHAWord alg)
      pmAsVWords =
        unconcatBitVector# paddedMessage

      -- group the words into message blocks
      pmAsVBlocks ∷
        Vec (PaddedMsgBits alg ℓ
               `Div` (MessageBlockWords * WordSize alg)) (MessageBlock alg)
      pmAsVBlocks =
        unconcat (SNat @MessageBlockWords) pmAsVWords

      -- apply the for loop "For i=1 to N:"
      hashValue ∷ HashValue alg
      hashValue = foldl computeBlock (_H⁰ alg) pmAsVBlocks
    in
      toDigest alg hashValue
 where
  -- perform the steps 1 to 4 for one iteration of the loop
  computeBlock ∷ HashValue alg → MessageBlock alg → HashValue alg
  computeBlock hb mb
    | SHAFacts ← knownSHA alg
    = -- step 4
      zipWith (+) hb
      -- steps 1 to 3
    $ snd $ foldl (&) (mb, hb) (computeCycles alg)

  lemma₀ ∷
    ∀ alg' n →
    Rewrite (PaddedMsgBits alg' n `Mod` BlockSize alg' ~ 0)
  lemma₀ _ _ = unsafeCoerce (Rewrite ∷ Rewrite (0 ~ 0))

  lemma₁ ∷
    ∀ alg' n →
    Rewrite (PaddedMsgBits alg' n `Mod` WordSize alg' ~ 0)
  lemma₁ _ _ = unsafeCoerce (Rewrite ∷ Rewrite (0 ~ 0))

  lemma₂ ∷
    ∀ alg' n →
    Rewrite (1 ≤ RequiredBlocks alg' n * BlockSize alg' - n `Mod` BlockSize alg')
  lemma₂ _ _ = unsafeCoerce (Rewrite ∷ Rewrite (0 ≤ 0))

  lemma₃ ∷
    ∀ alg' n →
    Rewrite (SizeBits alg'
            ≤ RequiredBlocks alg' n * BlockSize alg' - n `Mod` BlockSize alg' - 1)
  lemma₃ __ = unsafeCoerce (Rewrite ∷ Rewrite (0 ≤ 0))

-- | Truncates the resulting hash value to the left-most @n@ bits,
-- where @n@ is defined by the returned 'MessageDigestSize'.
toDigest ∷
  ∀ (alg ∷ SHA) → KnownSHA alg ⇒
  HashValue alg →
  BitVector (MessageDigestSize alg)
toDigest alg
  | SHAFacts ← knownSHA alg
  , u ← SNat @(HashValueWords alg * WordSize alg - 1)
  , l ← SNat @(HashValueWords alg * WordSize alg - MessageDigestSize alg)
  = slice u l . concatBitVector#

-- | The vector of computations performing
--
--  - Step "/1. Prepare the message schedule/"
--  - Step "/2. Initialize the five working variables/"
--  - Step "/3. For t=0 to .../"
computeCycles ∷
  ∀ (alg ∷ SHA) → KnownSHA alg ⇒
  Vec (ScheduleCount alg)
    ( (Vec MessageBlockWords (SHAWord alg), HashValue alg) →
      (Vec MessageBlockWords (SHAWord alg), HashValue alg)
    )
computeCycles alg
  | SHAFacts ← knownSHA alg
  = slidingWindowCycle alg <$> indicesI
