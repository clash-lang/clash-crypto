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
module Clash.Crypto.Cipher.AES.Streaming.Algorithm   
( Clash.Crypto.Cipher.AES.Streaming.Algorithm.cipher
  , Clash.Crypto.Cipher.AES.Streaming.Algorithm.invCipher
  , Clash.Crypto.Cipher.AES.Streaming.Algorithm.eqInvCipher
  , AESKeyExpansion(..)
  ) where




import Clash.Crypto.Cipher.AES.Specification.Types
import Clash.Crypto.Cipher.AES.Specification.Definitions
import Clash.Crypto.Cipher.AES.Specification as Spec
-- Interface liberies:
import Clash.Prelude
import Clash.Signal.Channel



import Data.Constraint.Nat.Extra (CancelMultiple, KeepsPositiveIfMultiple)
data CipherMode
  = CipherStart | CipherRounds (Index 4) Integer | CipherLast (Index 3) | CipherFin | CipherEnd
  deriving (Generic, NFDataX, Show, Eq)
cipher ∷ ∀ (alg ∷ AES) dom.
    ( Spec.KnownAES alg, HiddenClockResetEnable dom) ⇒
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
    put   (input1, w)
      | AESFacts{} <- knownAES @alg
      = ((input1, wInWords w), CipherStart)

    get ∷ (InType alg, WType alg) → ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode) -> OutType alg
    get _ ((output, _), _) = output
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
    ( Spec.KnownAES alg, HiddenClockResetEnable dom) ⇒
    Channel dom (InType alg, WType alg) →
    -- ^ input stream ^ key stream
    Channel dom (OutType alg)
    -- ^ response channel
eqInvCipher  input
  | AESFacts{} <- knownAES @alg
  = enhance put get compute input
  where
    wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
    wInWords words1
      | AESFacts{} <- knownAES @alg
      = reverse (unconcat (SNat ∷ SNat (Nb alg )) words1)

    put ∷ (InType alg, WType alg) →  ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode)
    put   (input1, w)
      | AESFacts{} <- knownAES @alg
      = ((input1, wInWords w), CipherStart)

    get ∷ (InType alg, WType alg) → ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode) -> OutType alg
    get _ ((output, _), _) = output
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
    ( Spec.KnownAES alg, HiddenClockResetEnable dom) ⇒
    Channel dom (InType alg, WType alg) →
    -- ^ input stream ^ key stream
    Channel dom (OutType alg)
    -- ^ response channel
invCipher  input
  | AESFacts{} <- knownAES @alg
  = enhance put get compute input
  where
    wInWords ∷ WType alg → Vec (Nr alg + 1) (RoundWType alg)
    wInWords words1
      | AESFacts{} <- knownAES @alg
      = reverse (unconcat (SNat ∷ SNat (Nb alg )) words1)

    put ∷ (InType alg, WType alg) →  ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode)
    put   (input1, w)
      | AESFacts{} <- knownAES @alg
      = ((input1, wInWords w), CipherStart)

    get ∷ (InType alg, WType alg) → ((InType alg, Vec (Nr alg + 1) (RoundWType alg)), CipherMode) -> OutType alg
    get _ ((output, _), _) = output
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
data KeyMode
  = KeyStart | KeyNew (Index 2) Integer | KeyLast (Index 4) Integer | KeyFin | KeyEnd
  deriving (Generic, NFDataX, Show, Eq)
class AESKeyExpansion (alg ∷ AES) where
    keyExpansion ∷ (Spec.KnownAES alg, HiddenClockResetEnable dom) ⇒
      Channel dom (KeyType alg) →
      -- ^ input stream ^ key stream
      Channel dom (WType alg)
      -- ^ response channel
instance AESKeyExpansion AES128 where
  keyExpansion ∷
      (Spec.KnownAES AES128, HiddenClockResetEnable dom) ⇒
      Channel dom (KeyType AES128) →
      -- ^ input stream ^ key stream
      Channel dom (WType AES128)
      -- ^ response channel
  keyExpansion = enhance put get compute
      where
        put ∷ ∀ alg. (Spec.KnownAES alg, alg ~ AES128) ⇒ KeyType alg →  ((KeyType alg, WordType alg, WType alg), KeyMode)
        put key -- state, result head00000 @key(1,2,3,4,5,...)  last (shiftInAtN will make it too front) and rotateRight key
          | AESFacts _ ← knownAES @alg
          = ((key, last key, repeat  @(((Nr alg + 1) * 4) -  Nk alg) (repeat  @(WordSize alg) (v2bv (repeat @(ByteSize alg) low))) ++ key), KeyStart)

        get ∷ ∀ alg. (Spec.KnownAES alg, alg ~ AES128) ⇒ KeyType alg → ((KeyType alg, WordType alg, WType alg), KeyMode) -> WType alg
        get _ ((_, _, w), _) = w
        compute ∷ ∀ alg. (Spec.KnownAES alg, alg ~ AES128) ⇒  KeyType alg → ((KeyType alg, WordType alg, WType alg), KeyMode) → CompMode ((KeyType alg, WordType alg, WType alg), KeyMode)
        compute _ (s0@(state, lastState, w), mode0) 
          | AESFacts alg ← knownAES @alg
          = (, mode0 /= KeyEnd) $ case mode0 of
          KeyEnd                             → (s0,                                                                             mode0)
          KeyFin                             → (s0,                                                                             KeyEnd)
          KeyStart                           → (s0,                                                                             KeyLast 3 (natToInteger @(Nr alg)))
          KeyLast 3 i                        → ((state, rotWord lastState ,w),                                                  KeyLast 2 i)
          KeyLast 2 i                        → ((state, subWord lastState ,w),                                                  KeyLast 1 i)
          KeyLast 1 i                        → ((state, xorWord lastState (_Rcon alg !! ((natToInteger @(Nr alg)) - i)),w),     KeyLast 0 i)
          KeyLast 0 i                        → ((postscanl xorWord lastState state, lastState , w),                             KeyNew 0 i)
          KeyNew 0 (0)                      → (s0,                                                                             KeyFin)
          KeyNew 0 i                         → ((state, last state, shiftNewPart w state),                                      KeyLast 3 (i - 1))
          
        shiftNewPart ∷ ∀ alg. (Spec.KnownAES alg, alg ~ AES128) ⇒ WType alg → KeyType alg -> WType alg
        shiftNewPart w state = fst (shiftInAtN w state)
-- instance AESKeyExpansion AES192 where
--   keyExpansion ∷
--       (Spec.KnownAES AES192, HiddenClockResetEnable dom) ⇒
--       Channel dom (KeyType AES192) →
--       -- ^ input stream ^ key stream
--       Channel dom (WType AES192)
--       -- ^ response channel
--   keyExpansion = enhance put get compute
--       where
--         put ∷ ∀ alg. (Spec.KnownAES alg, alg ~ AES192) ⇒ KeyType alg →  ((KeyType alg, WordType alg, WType alg), KeyMode)
--         put key -- state, result head00000 @key(1,2,3,4,5,...)  last (shiftInAtN will make it too front) and rotateRight key
--           | AESFacts _ ← knownAES @alg
--           -- TODO the solution shift too much.
--           = ((key, last key, repeat @(((Nr alg + 1) * 4) -  Nk alg) (repeat  @(WordSize alg) (v2bv (repeat @(ByteSize alg) low))) ++ key), KeyStart)

--         get ∷ ∀ alg. (Spec.KnownAES alg, alg ~ AES192) ⇒ KeyType alg → ((KeyType alg, WordType alg, WType alg), KeyMode) -> WType alg
--         get _ ((_, _, w), _) = w
--         compute ∷ ∀ alg. (Spec.KnownAES alg, alg ~ AES192) ⇒  KeyType alg → ((KeyType alg, WordType alg, WType alg), KeyMode) → CompMode ((KeyType alg, WordType alg, WType alg), KeyMode)
--         compute _ (s0@(state, lastState, w), mode0) 
--           | AESFacts alg ← knownAES @alg
--           = (, mode0 /= KeyEnd) $ case mode0 of
--           KeyEnd                             → (s0,                                                                             mode0)
--           KeyFin                             → (s0,                                                                             KeyEnd)
--           KeyStart                           → (s0,                                                                             KeyLast 3 (natToInteger @(Nr alg)))
--           KeyLast 3 i                        → ((state, rotWord lastState ,w),                                                  KeyLast 2 i)
--           KeyLast 2 i                        → ((state, subWord lastState ,w),                                                  KeyLast 1 i)
--           KeyLast 1 i                        → ((state, xorWord lastState (_Rcon alg !! ((natToInteger @(Nr alg)) - i)),w),     KeyLast 0 (i-1))
--           KeyLast 0 i                        → ((postscanl xorWord lastState state, lastState , w),                             KeyNew 0 i)
--           KeyNew 0 i                         → ((state, last state, shiftNewPart w state),                                      KeyLast 3 (i - 1))
--           KeyNew 0 (-1)                      → (s0,                                                                             KeyFin)
--         shiftNewPart ∷ ∀ alg. (Spec.KnownAES alg, alg ~ AES192) ⇒ WType alg → KeyType alg -> WType alg
--         shiftNewPart w state = fst (shiftInAtN w state)

-- instance AESKeyExpansion AES256 where
--   keyExpansion ∷
--       (Spec.KnownAES AES256, HiddenClockResetEnable dom) ⇒
--       Channel dom (KeyType AES256) →
--       -- ^ input stream ^ key stream
--       Channel dom (WType AES256)
--       -- ^ response channel
--   keyExpansion = enhance put get compute
--       where
--         put ∷ ∀ alg. (Spec.KnownAES alg, alg ~ AES256) ⇒ KeyType alg →  ((KeyType alg, WordType alg, WType alg), KeyMode)
--         put key -- state, result head00000 @key(1,2,3,4,5,...)  last (shiftInAtN will make it too front) and rotateRight key
--           | AESFacts _ ← knownAES @alg
--           = ((key, last key, repeat  @(((Nr alg + 1) * 4) -  Nk alg) (repeat  @(WordSize alg) (v2bv (repeat @(ByteSize alg) low))) ++ key), KeyStart)

--         get ∷ ∀ alg. (Spec.KnownAES alg, alg ~ AES256) ⇒ KeyType alg → ((KeyType alg, WordType alg, WType alg), KeyMode) -> WType alg
--         get _ ((_, _, w), _) = w
--         compute ∷ ∀ alg. (Spec.KnownAES alg, alg ~ AES256) ⇒  KeyType alg → ((KeyType alg, WordType alg, WType alg), KeyMode) → CompMode ((KeyType alg, WordType alg, WType alg), KeyMode)
--         compute _ (s0@(state, lastState, w), mode0) 
--           | AESFacts alg ← knownAES @alg
--           = (, mode0 /= KeyEnd) $ case mode0 of
--           KeyEnd                             → (s0,                                                                             mode0)
--           KeyFin                             → (s0,                                                                             KeyEnd)
--           KeyStart                           → (s0,                                                                             KeyLast 3 (natToInteger @(Nr alg)))
--           KeyLast 3 i                        → ((state, rotWord lastState ,w),                                                  KeyLast 2 i)
--           KeyLast 2 i                        → ((state, subWord lastState ,w),                                                  KeyLast 1 i)
--           KeyLast 1 i                        → ((state, xorWord lastState (_Rcon alg !! ((natToInteger @(Nr alg)) - i)),w),     KeyLast 0 (i-1))
--           -- TODO: There needs to be a subWord in between
--           KeyLast 0 i                        → ((postscanl xorWord lastState state, lastState , w),                             KeyNew 0 i)
--           KeyNew 0 i                         → ((state, last state, shiftNewPart w state),                                      KeyLast 3 (i - 1))
--           KeyNew 0 (-1)                      → (s0,                                                                             KeyFin)
--         shiftNewPart ∷ ∀ alg. (Spec.KnownAES alg, alg ~ AES256) ⇒ WType alg → KeyType alg -> WType alg
--         shiftNewPart w state = fst (shiftInAtN w state)



