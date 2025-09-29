{-|
Module      : Clash.Crypto.Cipher.AES.Streaming.Algorithm
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Algorithm implementation of FIPS 197 using the enchance methode
-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Clash.Crypto.Cipher.AES.Streaming.Algorithm where


import Data.Proxy (Proxy)
import Clash.Crypto.Cipher.AES.Specification.Types
import Clash.Crypto.Cipher.AES.Specification.Definitions
import Clash.Crypto.Cipher.AES.Specification
-- Interface liberies:
import Clash.Prelude
import Clash.Signal.Channel
import Clash.Signal.DataStream
import Clash.Signal.Extra (apWhen, regEnN)

import Data.Constraint.Nat.Extra (CancelMultiple, KeepsPositiveIfMultiple)
data CipherMode
  = CipherStart | CipherRounds (Index 4) Integer | CipherLast (Index 3) | CipherFin | CipherEnd
  deriving (Generic, NFDataX, Show, Eq)
cipher ∷ ∀ (alg ∷ AES) dom.
    ( KnownAES alg, HiddenClockResetEnable dom) ⇒
    Channel dom (InType alg, WType alg) →
    -- ^ input stream ^ key stream
    Channel dom (OutType alg)
    -- ^ response channel
cipher  input
  | AESFacts{} <- knownAES @alg
  = enhance put get compute input
  where
    wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
    wInWords 
      | AESFacts{} <- knownAES @alg
      = unconcat (SNat ∷ SNat (Nb alg ))

    put ∷ (InType alg, WType alg) →  ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode)
    put   (input, w)
      | AESFacts{} <- knownAES @alg
      = ((input, wInWords w), CipherStart)

    get ∷ (InType alg, WType alg) → ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode) -> OutType alg
    get _ (s0@(output, w), mode0) = output
    compute ∷ (InType alg, WType alg) → ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode) → CompMode ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode)
    compute _ (s0@(state, w), mode0) 
       | AESFacts{} ← knownAES @alg
       = (, mode0 /= CipherEnd) $ case mode0 of
      CipherEnd                          → (s0,                                    mode0)
      CipherFin                          → (s0,                                    CipherEnd)
      CipherStart                        → ((addRoundKey state (head w),w),        CipherRounds 3 (natToInteger @(Nr alg)))
      CipherRounds 3 1                   → (s0,                                    CipherLast 2)
      CipherRounds 3 i                   → ((subBytes state,w),                    CipherRounds 2 i)
      CipherRounds 2 i                   → ((shiftRows state,w),                   CipherRounds 1 i)
      CipherRounds 1 i                   → ((mixColumns state,w),                  CipherRounds 0 i)
      CipherRounds 0 i                   → ((addRoundKey state (w !! (((natToInteger @(Nr alg)) - i) + 1)),w),  CipherRounds 3 (i - 1))
      CipherLast 2                       → ((subBytes state,w),                    CipherLast 1)
      CipherLast 1                       → ((shiftRows state,w),                   CipherLast 0)
      CipherLast 0                       → ((addRoundKey state (last w),w),        CipherFin)

eqInvCipher ∷ ∀ (alg ∷ AES) dom.
    ( KnownAES alg, HiddenClockResetEnable dom) ⇒
    Channel dom (InType alg, WType alg) →
    -- ^ input stream ^ key stream
    Channel dom (OutType alg)
    -- ^ response channel
eqInvCipher  input
  | AESFacts{} <- knownAES @alg
  = enhance put get compute input
  where
    wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
    wInWords words
      | AESFacts{} <- knownAES @alg
      = reverse (unconcat (SNat ∷ SNat (Nb alg )) words)

    put ∷ (InType alg, WType alg) →  ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode)
    put   (input, w)
      | AESFacts{} <- knownAES @alg
      = ((input, wInWords w), CipherStart)

    get ∷ (InType alg, WType alg) → ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode) -> OutType alg
    get _ (s0@(output, w), mode0) = output
    compute ∷ (InType alg, WType alg) → ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode) → CompMode ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode)
    compute _ (s0@(state, w), mode0) 
       | AESFacts{} ← knownAES @alg
       = (, mode0 /= CipherEnd) $ case mode0 of
      CipherEnd                          → (s0,                                    mode0)
      CipherFin                          → (s0,                                    CipherEnd)
      CipherStart                        → ((invAddRoundKey state (head w),w),        CipherRounds 3 (natToInteger @(Nr alg)))
      CipherRounds 3 1                   → (s0,                                    CipherLast 2)
      CipherRounds 3 i                   → ((invSubBytes state,w),                    CipherRounds 2 i)
      CipherRounds 2 i                   → ((invShiftRows state,w),                   CipherRounds 1 i)
      CipherRounds 1 i                   → ((invMixColumns state,w),                  CipherRounds 0 i)
      CipherRounds 0 i                   → ((invAddRoundKey state (w !! (((natToInteger @(Nr alg)) - i) + 1)),w),  CipherRounds 3 (i - 1))
      CipherLast 2                       → ((invSubBytes state,w),                    CipherLast 1)
      CipherLast 1                       → ((invShiftRows state,w),                   CipherLast 0)
      CipherLast 0                       → ((invAddRoundKey state (last w),w),        CipherFin)
invCipher ∷ ∀ (alg ∷ AES) dom.
    ( KnownAES alg, HiddenClockResetEnable dom) ⇒
    Channel dom (InType alg, WType alg) →
    -- ^ input stream ^ key stream
    Channel dom (OutType alg)
    -- ^ response channel
invCipher  input
  | AESFacts{} <- knownAES @alg
  = enhance put get compute input
  where
    wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
    wInWords words
      | AESFacts{} <- knownAES @alg
      = reverse (unconcat (SNat ∷ SNat (Nb alg )) words)

    put ∷ (InType alg, WType alg) →  ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode)
    put   (input, w)
      | AESFacts{} <- knownAES @alg
      = ((input, wInWords w), CipherStart)

    get ∷ (InType alg, WType alg) → ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode) -> OutType alg
    get _ (s0@(output, w), mode0) = output
    compute ∷ (InType alg, WType alg) → ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode) → CompMode ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode)
    compute _ (s0@(state, w), mode0) 
       | AESFacts{} ← knownAES @alg
       = (, mode0 /= CipherEnd) $ case mode0 of
      CipherEnd                          → (s0,                                    mode0)
      CipherFin                          → (s0,                                    CipherEnd)
      CipherStart                        → ((invAddRoundKey state (head w),w),        CipherRounds 3 (natToInteger @(Nr alg)))
      CipherRounds 3 1                   → (s0,                                    CipherLast 2)
      CipherRounds 3 i                   → ((invShiftRows state,w),                    CipherRounds 2 i)
      CipherRounds 2 i                   → ((invSubBytes state,w),                   CipherRounds 1 i)
      CipherRounds 1 i                   → ((invAddRoundKey state (w !! (((natToInteger @(Nr alg)) - i) + 1)),w),                  CipherRounds 0 i)
      CipherRounds 0 i                   → ((invMixColumns state,w),  CipherRounds 3 (i - 1))
      CipherLast 2                       → ((invShiftRows state,w),                    CipherLast 1)
      CipherLast 1                       → ((invSubBytes state,w),                   CipherLast 0)
      CipherLast 0                       → ((invAddRoundKey state (last w),w),        CipherFin)


