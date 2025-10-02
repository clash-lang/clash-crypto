{-|
Module      : Clash.Crypto.Cipher.AES.Specification.Types
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Basic types covering the fundamentals of FIPS 197.
-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE NoTemplateHaskell #-}
{-# LANGUAGE NoGeneralizedNewtypeDeriving #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveAnyClass #-}
module Clash.Crypto.Cipher.AES.Specification.Types where

import Clash.Sized.BitVector (BitVector)
import Clash.Sized.Vector (Vec)
import Clash.Class.BitPack (BitPack)
import Clash.XException (NFDataX)
import Data.Eq (Eq)
import Data.Enum (Enum, Bounded)
import Data.Kind (Type)
import Data.Ord (Ord)
import Data.Typeable (Typeable)
import GHC.Show (Show)
import GHC.Generics (Generic)
import GHC.TypeLits
-- | Supported hash algorithms.
type AES ∷ Type
data AES =
    AES128
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

-- Definination according to table 1 hex
-- I don't think it is nessary
type NibbleSize ∷ AES → Nat
type family NibbleSize alg where
  NibbleSize _ = 4
type NibbleType (alg ∷ AES) = BitVector (NibbleSize alg)
type ByteSize (alg ∷ AES) = NibbleSize alg * 2
-- | The type of a word
type ByteType (alg ∷ AES) = BitVector (ByteSize alg)
type SplitByteType (alg ∷ AES) = Vec 2 (NibbleType alg)
-- | WordSize (in bytes) text chapter 5
type WordSize ∷ AES → Nat
type family WordSize alg where
  WordSize _ = 4
-- | The type of a word
type WordType (alg ∷ AES) = Vec (WordSize alg) (ByteType alg)

-- | Block size in words (defined in Table 3) and recommanded to be flexible 6.3.
type Nb ∷ AES → Nat
type family Nb alg where
  Nb _ = 4
-- | Block size in bits (defined in Table 3) and recommanded to be flexible 6.3.
type BlockSize (alg ∷ AES) = Nb alg * WordSize alg
-- | The type of a block
type BlockType (alg ∷ AES) = Vec (Nb alg) (WordType alg)
-- | To expliciet refer to a state defined in 3.4 ((first 8 bits) (second 8 bits) (third 8 bits) (fourth 8 bits))
type StateType (alg ∷ AES) = (BlockType alg)
-- | Key length in words (defined in Table 3) and recommanded to be flexible 6.3.
type Nk ∷ AES → Nat
type family Nk alg where
  Nk AES128 = 4
  Nk AES192 = 6
  Nk AES256 = 8
  Nk _      = 8
-- | Key length in bits (defined in Table 3) and recommanded to be flexible 6.3.
type KeyLength (alg ∷ AES) = Nk alg  GHC.TypeLits.* WordSize alg GHC.TypeLits.* ByteSize alg
-- | Key type based on the key length
type KeyType (alg ∷ AES) = Vec (Nk alg) (WordType alg)
-- | Number of rounds (defined in Table 3) and recommanded to be flexible 6.3.
type Nr ∷ AES → Nat
type family Nr alg where
  Nr AES128 = 10
  Nr AES192 = 12
  Nr AES256 = 14
  Nr _      = 14
-- | 5.1 state, w
-- since w always used in groups of 4 and cλash is not as good as python with indexes
-- and converting back and forth doesn't make any sense
type RoundWType (alg ∷ AES) = (BlockType alg)

type WType (alg ∷ AES) = Vec ((Nr alg + 1) * 4)  (WordType alg)

type NFixedWords ∷ AES → Nat

type family NFixedWords alg where
  NFixedWords _      = 10

type RconType  (alg ∷ AES) = Vec (NFixedWords alg) (WordType alg)
-- 3.4 definition of in, state, out
type InType (alg ∷ AES) = BlockType alg

type OutType (alg ∷ AES) = BlockType alg