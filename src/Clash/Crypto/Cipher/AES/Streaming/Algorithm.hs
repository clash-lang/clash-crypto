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
  , Clash.Crypto.Cipher.AES.Streaming.Algorithm.keyExpansionIEC
  , AESKeyExpansion(..)
  ) where

import Clash.Crypto.Cipher.AES.Specification.Types
import Clash.Crypto.Cipher.AES.Specification.Definitions
import Clash.Crypto.Cipher.AES.Specification as Spec

import Clash.Prelude
import Clash.Signal.Channel

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
  = KeyStart | KeyProsXOR (Index 3) Integer | KeyProsLastW (Index 4) Integer | KeyFin | KeyEnd
  deriving (Generic, NFDataX, Show, Eq)
class AESKeyExpansion (alg ∷ AES) where
    keyExpansion ∷ (KnownAES alg, HiddenClockResetEnable dom) ⇒
      Channel dom (KeyType alg) →
      --  ^ key stream
      Channel dom (WType alg)
      -- ^ response channel
instance AESKeyExpansion AES128 where
  keyExpansion ∷
      (KnownAES AES128, HiddenClockResetEnable dom) ⇒
      Channel dom (KeyType AES128) →
      --  ^ key stream
      Channel dom (WType AES128)
      -- ^ response channel
  keyExpansion = enhance put get compute
      where
        put ∷ ∀ alg. (KnownAES alg, alg ~ AES128) ⇒ KeyType alg →  ((KeyType alg, WordType alg, WType alg), KeyMode)
        put key -- state, result head00000 @key(1,2,3,4,5,...)  last (shiftInAtN will make it too front) and rotateRight key
          | AESFacts _ ← knownAES @alg
          = ((key, last key, repeat  @(((Nr alg + 1) * 4) -  Nk alg) (repeat  @(WordSize alg) (v2bv (repeat @(ByteSize alg) low))) ++ key), KeyStart)

        get ∷ ∀ alg. (KnownAES alg, alg ~ AES128) ⇒ KeyType alg → ((KeyType alg, WordType alg, WType alg), KeyMode) -> WType alg
        get _ ((_, _, w), _) = w
        compute ∷ ∀ alg. (KnownAES alg, alg ~ AES128) ⇒  KeyType alg → ((KeyType alg, WordType alg, WType alg), KeyMode) → CompMode ((KeyType alg, WordType alg, WType alg), KeyMode)
        compute _ (s0@(state, lastState, w), mode0) 
          | AESFacts alg ← knownAES @alg
          = (, mode0 /= KeyEnd) $ case mode0 of
          KeyEnd                             → (s0,                                                                             mode0)
          KeyFin                             → (s0,                                                                             KeyEnd)
          KeyStart                           → (s0,                                                                             KeyProsLastW 3 (natToInteger @(Nr alg)))
          KeyProsLastW 3 i                   → ((state, rotWord lastState ,w),                                                  KeyProsLastW 2 i)
          KeyProsLastW 2 i                   → ((state, subWord lastState ,w),                                                  KeyProsLastW 1 i)
          KeyProsLastW 1 i                   → ((state, xorWord lastState (_Rcon alg !! ((natToInteger @(Nr alg)) - i)),w),     KeyProsLastW 0 i)
          KeyProsLastW 0 i                   → ((postscanl xorWord lastState state, lastState , w),                             KeyProsXOR 0 i)
          KeyProsXOR 0 (0)                   → (s0,                                                                             KeyFin)
          KeyProsXOR 0 i                     → ((state, last state, shiftNewPart w state),                                      KeyProsLastW 3 (i - 1))
          
        shiftNewPart ∷ ∀ alg. (KnownAES alg, alg ~ AES128) ⇒ WType alg → KeyType alg -> WType alg
        shiftNewPart w state = fst (shiftInAtN w state)
instance AESKeyExpansion AES192 where
  keyExpansion ∷
      (KnownAES AES192, HiddenClockResetEnable dom) ⇒
      Channel dom (KeyType AES192) →
      -- ^ key stream
      Channel dom (WType AES192)
      -- ^ response channel
  keyExpansion = enhance put get compute
      where
        put ∷ ∀ alg. (KnownAES alg, alg ~ AES192) ⇒ KeyType alg →  ((KeyType alg, WordType alg, Vec (Nk alg * Nr alg) (WordType alg)), KeyMode)
        put key -- state, result head00000 @key(1,2,3,4,5,...)  last (shiftInAtN will make it too front) and rotateRight key
          | AESFacts _ ← knownAES @alg
          = ((key, last key, repeat  @(Nk alg * Nr alg - Nk alg) (repeat  @(WordSize alg) (v2bv (repeat @(ByteSize alg) low))) ++ key), KeyStart)

        get ∷ ∀ alg. (KnownAES alg, alg ~ AES192) ⇒ KeyType alg → ((KeyType alg, WordType alg, Vec (Nk alg * Nr alg) (WordType alg)), KeyMode) -> WType alg
        get _ ((_, _, w), _) = takeI w
         
        compute ∷ ∀ alg. (KnownAES alg, alg ~ AES192) ⇒  KeyType alg → ((KeyType alg, WordType alg, Vec (Nk alg * Nr alg) (WordType alg)), KeyMode) → CompMode ((KeyType alg, WordType alg, Vec (Nk alg * Nr alg) (WordType alg)), KeyMode)
        compute _ (s0@(state, lastState, w), mode0) 
          | AESFacts alg ← knownAES @alg
          = (, mode0 /= KeyEnd) $ case mode0 of
          KeyEnd                             → (s0,                                                                                  mode0)
          KeyFin                             → (s0,                                                                                  KeyEnd)
          KeyStart                           → (s0,                                                                                  KeyProsLastW 3 (natToInteger @(Nr alg)))
          KeyProsLastW 3 i                   → ((state, rotWord lastState ,w),                                                       KeyProsLastW 2 i)
          KeyProsLastW 2 i                   → ((state, subWord lastState ,w),                                                       KeyProsLastW 1 i)
          KeyProsLastW 1 i                   → ((state, xorWord lastState (_Rcon alg !! ((natToInteger @(Nr alg)) - i)),w),          KeyProsLastW 0 i)
          KeyProsLastW 0 i                   → ((postscanl xorWord lastState state, lastState , w),                                  KeyProsXOR 0 i)
          KeyProsXOR 0 (1)                   → (s0,                                                                                  KeyFin)
          KeyProsXOR 0 i                     → ((state, last state, shiftNewPart w state),                                           KeyProsLastW 3 (i - 1))
          
        shiftNewPart ∷ ∀ alg. (KnownAES alg, alg ~ AES192) ⇒ Vec (Nk alg * Nr alg) (WordType alg) → KeyType alg -> Vec (Nk alg * Nr alg) (WordType alg)
        shiftNewPart w state = fst (shiftInAtN w state)

instance AESKeyExpansion AES256 where
  keyExpansion ∷
      (KnownAES AES256, HiddenClockResetEnable dom) ⇒
      Channel dom (KeyType AES256) →
      -- ^ key stream
      Channel dom (WType AES256)
      -- ^ response channel
  keyExpansion = enhance put get compute
      where
        put ∷ ∀ alg. (KnownAES alg, alg ~ AES256) ⇒ KeyType alg →  ((KeyType alg, WordType alg, Vec (Nk alg * Nr alg) (WordType alg)), KeyMode)
        put key -- state, result head00000 @key(1,2,3,4,5,...)  last (shiftInAtN will make it too front) and rotateRight key
          | AESFacts _ ← knownAES @alg
          = ((key, last key, repeat  @(Nk alg * Nr alg - Nk alg) (repeat  @(WordSize alg) (v2bv (repeat @(ByteSize alg) low))) ++ key), KeyStart)

        get ∷ ∀ alg. (KnownAES alg, alg ~ AES256) ⇒ KeyType alg → ((KeyType alg, WordType alg, Vec (Nk alg * Nr alg) (WordType alg)), KeyMode) -> WType alg
        get _ ((_, _, w), _) = takeI w
         
        compute ∷ ∀ alg. (KnownAES alg, alg ~ AES256) ⇒  KeyType alg → ((KeyType alg, WordType alg, Vec (Nk alg * Nr alg) (WordType alg)), KeyMode) → CompMode ((KeyType alg, WordType alg, Vec (Nk alg * Nr alg) (WordType alg)), KeyMode)
        compute _ (s0@(state, lastState, w), mode0) 
          | AESFacts alg ← knownAES @alg
          = (, mode0 /= KeyEnd) $ case mode0 of
          KeyEnd                             → (s0,                                                                                  mode0)
          KeyFin                             → (s0,                                                                                  KeyEnd)
          KeyStart                           → (s0,                                                                                  KeyProsLastW 3 (natToInteger @(Nr alg)))
          KeyProsLastW 3 i                   → ((state, rotWord lastState ,w),                                                       KeyProsLastW 2 i)
          KeyProsLastW 2 i                   → ((state, subWord lastState ,w),                                                       KeyProsLastW 1 i)
          KeyProsLastW 1 i                   → ((state, xorWord lastState (_Rcon alg !! ((natToInteger @(Nr alg)) - i)),w),          KeyProsLastW 0 i)
          KeyProsLastW 0 i                   → ((firstPart state lastState, lastState , w),                                          KeyProsXOR 2 i)
          KeyProsXOR 0 (1)                   → (s0,                                                                                  KeyFin)
          KeyProsXOR 2 i                     → ((state, subWord (last (firstSplit state)) , w),                                      KeyProsXOR 1 i)
          KeyProsXOR 1 i                     → ((secondPart state lastState, lastState , w),                                         KeyProsXOR 0 i)
          KeyProsXOR 0 i                     → ((state, last state, shiftNewPart w state),                                           KeyProsLastW 3 (i - 1))
        firstSplit = takeI @(Nk AES256 `Div` 2)
        secondSplit = dropI @(Nk AES256 `Div` 2)
        firstPart state lastState =  postscanl xorWord lastState (firstSplit state) ++ secondSplit state
        secondPart state lastState = firstSplit state ++ postscanl xorWord lastState (secondSplit state)
        shiftNewPart ∷ ∀ alg. (KnownAES alg, alg ~ AES256) ⇒ Vec (Nk alg * Nr alg) (WordType alg) → KeyType alg -> Vec (Nk alg * Nr alg) (WordType alg)
        shiftNewPart ws state = fst (shiftInAtN ws state)

        



keyExpansionIEC ∷ ∀ (alg ∷ AES) dom.
      (KnownAES alg, AESKeyExpansion alg, HiddenClockResetEnable dom) ⇒
      Channel dom (KeyType alg) →
      -- ^ key stream
      Channel dom (WType alg)
      -- ^ response channel
keyExpansionIEC input 
      | AESFacts alg ← knownAES @alg
      = enhance put get compute (Clash.Crypto.Cipher.AES.Streaming.Algorithm.keyExpansion @alg input)
      where 
        put ∷ WType alg →  ((Vec 1 (RoundWType alg), Vec (Nr alg - 1) (RoundWType alg), Vec 1 (RoundWType alg)), KeyMode)
        put w
          | AESFacts{} ← knownAES @alg
          = ((head wInWords:>Nil , init (tail wInWords), last wInWords:>Nil), KeyStart)
            where 
                wInWords ∷ Vec (Nr alg + 1) (RoundWType alg)
                wInWords 
                    | AESFacts{} ← knownAES @alg
                    = unconcat (SNat ∷ SNat (Nb alg )) w

        get ∷ (KnownAES alg) ⇒ WType alg → ((Vec 1 (RoundWType alg), Vec (Nr alg - 1) (RoundWType alg), Vec 1 (RoundWType alg)), KeyMode) -> WType alg
        get _ ((start, middle, end), _) 
             | AESFacts alg ← knownAES @alg
              =  concat (start  ++ middle ++ end)
         
        compute ∷ (KnownAES alg) ⇒  WType alg → ((Vec 1 (RoundWType alg), Vec (Nr alg - 1) (RoundWType alg), Vec 1 (RoundWType alg)), KeyMode) → CompMode  ((Vec 1 (RoundWType alg), Vec (Nr alg - 1) (RoundWType alg), Vec 1 (RoundWType alg)), KeyMode)
        compute _ (s0@(start, middle, end), mode0) 
          | AESFacts alg ← knownAES @alg
          = (, mode0 /= KeyEnd) $ case mode0 of
          KeyEnd                             → (s0,                                                                                  mode0)
          KeyFin                             → (s0,                                                                                  KeyEnd)
          KeyStart                           → ((start,map invMixColumns middle,end),                                                KeyFin)



