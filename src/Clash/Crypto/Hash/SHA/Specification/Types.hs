{-|
Module      : Clash.Crypto.Hash.SHA.Specification.Types
Copyright   : Copyright © 2024 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Basic types covering the fundamentals of FIPS 180-4.
-}

{-# LANGUAGE NoTemplateHaskell #-}
{-# LANGUAGE NoGeneralizedNewtypeDeriving #-}
{-# LANGUAGE Safe #-}

module Clash.Crypto.Hash.SHA.Specification.Types where

import Clash.Sized.BitVector (BitVector)
import Clash.Sized.Vector (Vec)
import Data.Kind (Type)
import GHC.TypeNats (Nat)

-- | Supported hash algorithms.
type SHA ∷ Type
data SHA =
    SHA1
  | SHA224
  | SHA256
  | SHA384
  | SHA512
  | SHA512224
  | SHA512256

-- | Word size in bits (defined in Figure 1).
type WordSize ∷ SHA → Nat
type family WordSize alg where
  WordSize SHA1   = 32
  WordSize SHA224 = 32
  WordSize SHA256 = 32
  WordSize _      = 64

-- | Block size in bits (defined in Figure 1).
type BlockSize ∷ SHA → Nat
type family BlockSize alg where
  BlockSize SHA1   = 512
  BlockSize SHA224 = 512
  BlockSize SHA256 = 512
  BlockSize _      = 1024

-- | Message digest size in bits (defined in Figure 1).
type MessageDigestSize ∷ SHA → Nat
type family MessageDigestSize alg where
  MessageDigestSize SHA1      = 160
  MessageDigestSize SHA224    = 224
  MessageDigestSize SHA256    = 256
  MessageDigestSize SHA384    = 384
  MessageDigestSize SHA512    = 512
  MessageDigestSize SHA512224 = 224
  MessageDigestSize SHA512256 = 256

-- | The number of words representing a hash value (defined in the
-- first paragraphs of the sections 6.1, 6.2, and 6.4, respectively).
type HashValueWords ∷ SHA → Nat
type family HashValueWords alg where
  HashValueWords SHA1 = 5
  HashValueWords _    = 8

-- | The number of message schedules (defined in the first paragraphs
-- of the sections 6.1, 6.2, and 6.4, respectively).
type ScheduleCount ∷ SHA → Nat
type family ScheduleCount alg where
  ScheduleCount SHA224 = 64
  ScheduleCount SHA256 = 64
  ScheduleCount _      = 80

-- | The "SHA Word" type.
type SHAWord (alg ∷ SHA) = BitVector (WordSize alg)

-- | The "Message Block" type.
type MessageBlock (alg ∷ SHA) =
  Vec 16 (SHAWord alg)

-- | The "Hash Value" type (defined in the first paragraphs of
-- the sections 6.1, 6.2, and 6.4, respectively).
type HashValue (alg ∷ SHA) =
  Vec (HashValueWords alg) (SHAWord alg)

-- | The "Message" type.
type Message (ℓ ∷ Nat) = BitVector ℓ
