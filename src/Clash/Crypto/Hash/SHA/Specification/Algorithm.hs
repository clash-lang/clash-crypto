{-|
Module      : Clash.Crypto.Hash.SHA.Specification.Algorithm
Copyright   : Copyright © 2024 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Algorithmic reference implementation of FIPS 180-4 using a purely
functional description.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}

module Clash.Crypto.Hash.SHA.Specification.Algorithm
  ( hash
  , computeCycles
  , toDigest
  ) where

import Clash.Prelude

import Data.Function ((&))
import Data.Constraint (Dict(..))
import Language.Haskell.Unicode (type (≤))
import Unsafe.Coerce (unsafeCoerce)

import Clash.Crypto.Hash.SHA.Specification.Types
import Clash.Crypto.Hash.SHA.Specification.Definitions
import Clash.Crypto.Hash.SHA.Specification.Properties
import Data.Constraint.Nat.Extra

-- | Purely functional reference implementation of the hashing
-- algorithms defined in FIPS 180-4.
hash ∷
  ∀ (alg ∷ SHA) (ℓ ∷ Nat).
  (KnownSHA alg, KnownNat ℓ) ⇒
  Message ℓ →
  -- ^ input message
  BitVector (MessageDigestSize alg)
  -- ^ resulting message digest
hash msg
  | SHAFacts alg ← knownSHA @alg
  , Dict ← modBound @ℓ @(BlockSize alg)
  , Dict ← condMonotone @1 @1 @2
      @(1 + SizeBits alg <=? BlockSize alg - ℓ `Mod` BlockSize alg)
  , Dict ← timesMonotoneRight
      @(RequiredBlocks alg ℓ)
      @(BlockSize alg)
      @(BlockSize alg)
  , Dict ← leTrans
      @(ℓ `Mod` BlockSize alg)
      @(BlockSize alg)
      @(RequiredBlocks alg ℓ * BlockSize alg)
  , Dict ← lemma₀ @alg @ℓ
  , Dict ← lemma₁ @alg @ℓ
  , Dict ← lemma₂ @alg @ℓ
  , Dict ← lemma₃ @alg @ℓ
  , Dict ← cancelMultiple @(PaddedMsgBits alg ℓ) @(WordSize alg)
  , Dict ← cancelFactor @(PaddedMsgBits alg ℓ) @(WordSize alg) @16
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
        Vec (PaddedMsgBits alg ℓ `Div` (16 * WordSize alg)) (MessageBlock alg)
      pmAsVBlocks =
        unconcat (SNat @16) pmAsVWords

      -- apply the for loop "For i=1 to N:"
      hashValue ∷ HashValue alg
      hashValue = foldl computeBlock (_H⁰ alg) pmAsVBlocks
    in
      toDigest @alg hashValue
 where
  -- perform the steps 1 to 4 for one iteration of the loop
  computeBlock ∷ HashValue alg → MessageBlock alg → HashValue alg
  computeBlock hb mb
    | SHAFacts{} ← knownSHA @alg
    = -- step 4
      zipWith (+) hb
      -- steps 1 to 3
    $ foldl (&) hb (($ mb) <$> computeCycles @alg)

  lemma₀ ∷
    ∀ alg' n.
    Dict (PaddedMsgBits alg' n `Mod` BlockSize alg' ~ 0)
  lemma₀ =
    unsafeCoerce (Dict ∷ Dict (0 ~ 0))

  lemma₁ ∷
    ∀ alg' n.
    Dict (PaddedMsgBits alg' n `Mod` WordSize alg' ~ 0)
  lemma₁ =
    unsafeCoerce (Dict ∷ Dict (0 ~ 0))

  lemma₂ ∷
    ∀ alg' n.
    Dict (1 ≤ RequiredBlocks alg' n * BlockSize alg' - n `Mod` BlockSize alg')
  lemma₂ =
    unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  lemma₃ ∷
    ∀ alg' n.
    Dict (SizeBits alg'
            ≤ RequiredBlocks alg' n * BlockSize alg' - n `Mod` BlockSize alg' - 1)
  lemma₃ =
    unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

-- | Truncates the resulting hash value to the left-most @n@ bits,
-- where @n@ is defined by the returned 'MessageDigestSize'.
toDigest ∷
  ∀ (alg ∷ SHA). KnownSHA alg ⇒
  HashValue alg →
  BitVector (MessageDigestSize alg)
toDigest
  | SHAFacts _ ← knownSHA @alg
  = slice
      (SNat @(HashValueWords alg * WordSize alg - 1))
      (SNat @(HashValueWords alg * WordSize alg - MessageDigestSize alg))
  . concatBitVector#

-- | The vector of computations performing
--
--  - Step "/1. Prepare the message schedule/"
--  - Step "/2. Initialize the five working variables/"
--  - Step "/3. For t=0 to .../"
computeCycles ∷
  ∀ (alg ∷ SHA). KnownSHA alg ⇒
  Vec (ScheduleCount alg) (MessageBlock alg → HashValue alg → HashValue alg)
computeCycles
  | SHAFacts alg ← knownSHA @alg
  = smapWithBounds @(ScheduleCount alg) (\t a → computeCycle a t)
  $ repeat @(ScheduleCount alg - 1 + 1) alg
