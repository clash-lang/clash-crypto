{-|
Module      : Clash.Crypto.Cipher.AES.Specification.Types
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Basic types covering the fundamentals of FIPS 197.
-}

{-# LANGUAGE Safe #-}

module Clash.Crypto.Cipher.AES.Specification.Types where

import Clash.Sized.BitVector (BitVector)
import Clash.Sized.Vector (Vec)
import Clash.Class.BitPack (BitPack(..))
import Clash.XException (NFDataX)
import Data.Eq (Eq)
import Data.Enum (Enum, Bounded)
import Data.Kind (Type)
import Data.Ord (Ord)
import Data.Typeable (Typeable)
import GHC.Show (Show)
import GHC.Generics (Generic)
import GHC.TypeLits (Nat, type (*), type (+))

-- | Supported AES ciphers.
type AES ∷ Type
data AES
  = AES128
  | AES192
  | AES256
  deriving
    ( Generic
    , NFDataX
    , BitPack
    , Eq
    , Ord
    , Show
    , Enum
    , Bounded
    , Typeable
    )

-- | A sequence of eight bits.
type Byte = BitVector 8

-- | The number of bytes forming a word.
type AESWordByteCount = 4

-- | A group of 32 bits that is treated either as a single entity or
-- as an array of 4 bytes.
type AESWord = Vec AESWordByteCount Byte

-- | The key length in words, as defined in Table 3 and recommended to
-- be flexible in Section 6.3.
type Nk ∷ AES → Nat
type family Nk alg where
  Nk AES128 = 4
  Nk AES192 = 6
  Nk AES256 = 8

-- | The block size in words, as defined in Table 3 and recommended to
-- be flexible in Section 6.3.
type Nb ∷ AES → Nat
type Nb alg = 4

-- | The number of rounds, as defined in Table 3 and recommended to be
-- flexible in Section 6.3.
type Nr ∷ AES → Nat
type family Nr alg where
  Nr AES128 = 10
  Nr AES192 = 12
  Nr AES256 = 14

-- | The block size in bytes, as defined in Table 3 and recommended to
-- be flexible in Section 6.3.
type AESBlockByteCount (alg ∷ AES) = Nb alg * AESWordByteCount

-- | A sequence of bits of a given fixed length. In FIPS 197, blocks
-- consist of 128 bits, sometimes represented as arrays of bytes or
-- words.
type AESBlock (alg ∷ AES) = Vec (Nb alg) AESWord

-- | Intermediate result of the AES block cipher that is represented
-- as a two-dimensional array of bytes with four rows and /Nb/ columns.
type AESState (alg ∷ AES) = AESBlock alg

-- | The parameter of a block cipher that determines the selection of
-- a permutation from the block cipher family.
type AESKey (alg ∷ AES) = Vec (Nk alg) AESWord

-- | One of the /Nr + 1/ arrays of four words that are derived from
-- the block cipher key using the key expansion routine.
type AESRoundKey (alg ∷ AES) = AESBlock alg

-- | The sequence of round keys that are generated from the key by
-- @KeyExpansion()@.
type KeySchedule (alg ∷ AES) = Vec ((Nr alg + 1) * 4) AESWord

-- | The number of round constants according to Table 5.
type RoundConstantCount = 10

-- | The round constants according to Table 5.
type RoundConstants = Vec RoundConstantCount AESWord
