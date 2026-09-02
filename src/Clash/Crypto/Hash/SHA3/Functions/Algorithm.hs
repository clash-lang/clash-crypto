{-|
Module      : Clash.Crypto.Hash.SHA3.Functions.Algorithm
Copyright   : Copyright © 2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Definitions of the hashing function purely algorithmically.
-}
{-# LANGUAGE MagicHash #-}

module Clash.Crypto.Hash.SHA3.Functions.Algorithm
  ( sponge
  , absorb
  , spongeSqueeze
  , keccakc
  , sha3
  )
  where

import Clash.Prelude

import GHC.TypeNats.Proof
import Language.Haskell.Unicode (type (≤))

import Data.Constraint.Nat.Extra
  ( CancelMultiple
  , ModBound
  , LtImpliesLE
  , Pad10s1Property
  , DividentLESucDivTimesDivisor
  , SubOfPosIsLT
  , SubOfLTIsPos
  )
import Clash.Crypto.Hash.SHA3.State (KnownStateL, StateSize, StateArray)
import Clash.Crypto.Hash.SHA3.Types
import Clash.Crypto.Hash.SHA3.Properties
  ( KnownSHA3 (..)
  , SuffixConstants (..)
  , SHA3Facts (..))
import Clash.Crypto.Hash.SHA3.Functions.Padding (pad101)
import Clash.Crypto.Hash.SHA3.Functions.Permutations
  (keccakp, trunc, truncLT, reverseBitsInBytes)

-- | A functional implementation of
-- the sponge function, as defined in FIPS-202.
sponge ∷
  ∀ (l ∷ Nat) (len ∷ Nat). (KnownStateL l, KnownNat len) ⇒
  -- ^ The StateL and the message size.
  ∀ (d ∷ Nat). (KnownNat d, 1 ≤ d) ⇒
  -- ^ The required output digest size.
  ∀ (r ∷ Nat) → (KnownNat r, 1 ≤ r, r < StateSize l) ⇒
  -- ^ The absorb rate.
  (StateArray l → StateArray l) →
  -- ^ The function to use for the absorbing and squeezing.
  (
    ∀ (x ∷ Nat) → (KnownNat x, 1 ≤ x) ⇒
    ∀ (m ∷ Nat) → (KnownNat m) ⇒
    BitVector (Pad101Size x m)
  ) →
  -- ^ The padding to be added to the message.
  Message len →
  -- ^ Input message.
  BitVector d
  -- ^ The result of the sponge function.
sponge r f pad msg
  | Rewrite ← using @(ModBound (len + 2) r)
  , Rewrite ← using @(Pad10s1Property r len)
  , Rewrite ← using @(CancelMultiple (len + Pad101Size r len) r)
  = let
      -- First we pad the message
      paddedMessage ∷ BitVector (len + Pad101Size r len)
      paddedMessage = msg ++# pad r len

      -- Split the padded message into a words
      -- This is possible from the definition of the padding
      pmAsVWords ∷
        Vec ((len + Pad101Size r len) `Div` r) (BitVector r)
      pmAsVWords = unpack paddedMessage
      
      -- The initial state is zero
      sInit = zeroBits ∷ StateArray l
      -- Absorb all the input in the state
      s = foldl (absorb r f) sInit pmAsVWords
    in spongeSqueeze r f s

-- | A function that absorbs the input of length @r@
-- to the given state of length @b@, using @f@,
-- to produce the new state.
absorb ∷
  ∀ (l ∷ Nat). KnownStateL l ⇒
  ∀ (r ∷ Nat) → (KnownNat r, 1 ≤ r, r < StateSize l) ⇒
  (StateArray l → StateArray l) →
  StateArray l →
  BitVector r →
  StateArray l
absorb r f state input
  | Rewrite ← using @(LtImpliesLE r (StateSize l))
  = let cZeros = zeroBits ∷ BitVector (StateSize l - r)
    in f (state `xor` (input ++# cZeros))

type SpongeSqueezeRMultiples d r = (d `Div` r) + 1

-- | A function that performs the squeeze operation
-- on the state to produce the result of length @d@.
spongeSqueeze ∷
  ∀ (l ∷ Nat) (d ∷ Nat). KnownStateL l ⇒
  ∀ (r ∷ Nat) → (KnownNat r, 1 ≤ r, r < StateSize l) ⇒
  (StateArray l → StateArray l) →
  (KnownNat d, 1 ≤ d) ⇒
  StateArray l →
  BitVector d
spongeSqueeze r f state
  | Rewrite ← using @(DividentLESucDivTimesDivisor d r)
  , Rewrite ← using @(LtImpliesLE r (StateSize l))
  =
  let
    -- Initially we have an empty vector Z
    -- We want to fill it by writting Truncᵣ(S) ∷ BitVector r repeatedly
    zInit ∷ Vec (SpongeSqueezeRMultiples d r) (BitVector r)
    zInit = repeat 0
    -- We fold over vector to fill it using the previously computed S
    ffold (s, zAux) i _ = (f s, replace i (truncLT r s) zAux)
    (_, zFinal) = ifoldl ffold (state, zInit) zInit
    -- We concat the vector into a BitVector of length ((Div d r + 1) * r)
    z = pack zFinal
    -- We return Trunc_d(Z)
  in trunc d z

-- | A functional implementation of the KECCAK[c] function.
keccakc ∷
  ∀ (len ∷ Nat) (d ∷ Nat).
  (KnownNat len, KnownNat d, 1 ≤ d) ⇒
  ∀ (c ∷ Nat) → (KnownNat c, 1 <= c, c < StateSize 6) ⇒
  Message len →
  BitVector d
keccakc c msg
  | Rewrite ← using @(SubOfPosIsLT (StateSize 6) c)
  , Rewrite ← using @(SubOfLTIsPos (StateSize 6) c)
  = sponge @6 @len @d (Rate (StateSize 6) c) f pad101 msg
 where
  f state = keccakp @6 24 state

-- | A functional implementation of any SHA3 function.
sha3# ∷
  ∀ (l ∷ Nat). KnownNat l ⇒
  ∀ (alg ∷ SHA3) → KnownSHA3 alg ⇒
  Message l →
  Digest alg
sha3# alg msg
  | SHA3Facts ← knownSHA3 alg
  = keccakc
      (AlgCapacity alg)
      (msg ++# suffix alg)

-- | A functional implementation of any SHA3 function
-- where the input is aligned in bytes.
-- In the result, in each byte the msb is the right-most bit.
sha3 ∷
  ∀ (l ∷ Nat). (KnownNat l, l `Mod` 8 ~ 0) ⇒
  ∀ (alg ∷ SHA3) → KnownSHA3 alg ⇒
  Message l →
  Digest alg
sha3 alg msg
  | SHA3Facts ← knownSHA3 alg
  = reverseBitsInBytes $ sha3# alg (reverseBitsInBytes msg)
