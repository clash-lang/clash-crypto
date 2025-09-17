{-|
Module      : Clash.Crypto.Blockcipher.AES.Specification.Definitions
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Basic definitions covering the fundamentals of FIPS 197.
-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}

module Clash.Crypto.Cipher.AES.Specification.Definitions where


import Clash.Prelude
import Data.Proxy (Proxy)

import Clash.Crypto.Cipher.AES.Specification.Types
import Clash.Crypto.Cipher.AES.Specification.Constants

import GHC.TypeLits ()
-- Explanation of infix can be found here https://www.haskell.org/onlinereport/decls.html#prelude-fixities
-- It is basically defining the ordering of execution. 9 is used standard.

-------------------------------------------
-- Section 3: Notation and Conventions   --
-------------------------------------------
-- | From input to state conversion methode, but this inherited in haskell from 3.4
-- in2s
-- s2out
-- | Not implement expect it to be not needed and be done by Cλash compiler

-- State = [word1, word2, word3, word4]
-- thus words are split at:
-- | $s_{0,0}$ | split |$s_{0,1}$ | split |$s_{0,2}$ |split | $s_{0,3}$ |
-- | $s_{1,0}$ | split |$s_{1,1}$ | split |$s_{1,2}$ |split | $s_{1,3}$ |
-- | $s_{2,0}$ | split |$s_{2,1}$ | split |$s_{2,2}$ |split | $s_{2,3}$ |
-- | $s_{3,0}$ | split |$s_{3,1}$ | split |$s_{3,2}$ |split | $s_{3,3}$ |

-------------------------------------------
-- Section 4: Preliminaries              --
-------------------------------------------
-- Section 4.1: Addition in GF(2⁸)
(⊕) ∷ KnownNat w ⇒ BitVector w → BitVector w → BitVector w
(⊕) = xor
-- Section 4.2: Multiplication in GF(2⁸)


xTimes ∷  (KnownNat w) ⇒ BitVector w → BitVector w
xTimes a =  if y == 0x01 then z ⊕ resize mX else z
    where x = finiteBitSize a - 1
          y = shiftR a x
          z = resize (a .<<+ 0)

-- To convert BitVector to vector bv2v, and v2bv.

-- | Section 4.2: Multiplication in GF(2⁸), the documentation suggests that we use xTimes
-- | to generate by successsibely applying xTimes(), since there is a module 0x57 envolved
-- | the result will be no bigger then 0x57 thus not bigger as 1 byte.
-- | Equation 4.4
(•) ∷ (KnownNat w) ⇒ BitVector w →  BitVector w →  BitVector w
(•) b c = foldl (⊕) (0x00) (zipWith (\f g →  if f then g else (0x00)) (bv2vbool b) (list_xtimes c))
    where
        list_xtimes ∷  (KnownNat n, KnownNat w) ⇒ BitVector w → Vec n (BitVector w)
        list_xtimes = iterateI xTimes
        -- | function that transform from bitvector to vector of booleans.
        bv2vbool ∷  (KnownNat w) ⇒ BitVector w → Vec w Bool
        bv2vbool b1 = fmap (testBit b1) (iterateI (+1) 0)



-- | Section 4.3: Multiplication of Words by a Fixed Matrix in GF(2⁸)
-- | Generic multiplication
matrixMultiplication ∷ (KnownNat w, KnownNat m, KnownNat n) ⇒ Vec m (Vec n (BitVector w)) → Vec n (BitVector w) → Vec m (BitVector w)
matrixMultiplication a b = fmap (vectorMultiplication b) a
    where
        vectorMultiplication ∷ (KnownNat w, KnownNat n) ⇒  Vec n (BitVector w) → Vec n (BitVector w) → BitVector w
        vectorMultiplication b1 a1 = foldl (⊕) 0x00  (zipWith (•) b1 a1)

-- | Multiplication as defined in equation 4.9
-- | Matrix multiplication based on two vectors as neded MixColumns() and InvMixColumns()
vectorMatrixMultiplication :: (KnownNat w, KnownNat n) => Vec n (BitVector w) -> Vec n (BitVector w) -> Vec n (BitVector w)
vectorMatrixMultiplication a = matrixMultiplication (generateMatrixA a)
    where
        generateMatrixA :: (KnownNat w, KnownNat n) =>  Vec n (BitVector w) -> Vec n (Vec n (BitVector w))
        generateMatrixA a1 = transpose (iterateI (`rotateRight` (1 ∷ Integer)) a1)

-- | Section 4.3:
-- | inverse based of 4.11
inv :: (KnownNat w) =>
     BitVector w -> BitVector w
inv b = foldl (•) 0X01 (list_binary_powers b)
    where
        pow2 :: KnownNat w => BitVector w -> BitVector w
        pow2 b1 = (•) b1 b1
        list_binary_powers :: (KnownNat w) => BitVector w -> Vec w (BitVector w)
        list_binary_powers = generateI pow2
-- | TODO: A faster inverse can be implemented with extended ecuclidean algorithm

 -- TODO:
-- | Round constansts Rcon is a set of 10 set fixed words and it will be invoked by KEYEXPANSION


-------------------------------------------
-- Section 5: Algorithm Specifcations    --
-------------------------------------------
--------------------------------------------------------------------------------------
-- Section 5.1 and 5.3: Cipher and invCipher support functions                      --
--------------------------------------------------------------------------------------
-- | Definitions for cipher
-- _AddRoundKey
-- Shift test 
-- Clash.Crypto.Cipher.AES.Specification.Definitions.invShiftRows ( Clash.Crypto.Cipher.AES.Specification.Definitions.shiftRows Clash.Crypto.Cipher.AES.Specification.Definitions.test_matrix)
-- should give the same back.
-- Similiar for mixcolumns
--  Clash.Crypto.Cipher.AES.Specification.Definitions.invMixColumns ( Clash.Crypto.Cipher.AES.Specification.Definitions.mixColumns Clash.Crypto.Cipher.AES.Specification.Definitions.test_matrix)

-- | 5.1.1 subBytes() (equation 5.2, 5.3, 5.4) but implemented with table 4
subBytes ∷ StateType alg → StateType alg
subBytes = map (map (sBox xySBox))
-- | the methode to select the right value from sBox that is given with it. 
sBox ∷ Vec (2 * ByteSize alg) (Vec (2 * ByteSize alg) (ByteType alg)) → ByteType alg → ByteType alg
sBox m a = (m !! x_part a (0 ∷ Integer))  !! x_part a (1 ∷ Integer)
    where
        splitBitVector ∷ ByteType alg → SplitByteType alg -- Binding such that the rest also works.
        splitBitVector = unconcatBitVector#
        x_part ∷ (Enum i) ⇒ ByteType alg → i → NibbleType alg
        x_part b c = splitBitVector b !! c

-- | 5.1.2 shiftRows() (equation 5.5)
shiftRows ∷ StateType alg → StateType alg
shiftRows state = transpose (zipWith rotateLeft (transpose state) (iterateI (+1) (0 ∷ Integer)))

-- | 5.1.3 mixColumns() (equation 5.7, 5.8)
mixColumns ∷ StateType alg → StateType alg
mixColumns = fmap (vectorMatrixMultiplication aMixColumns)

-- | 5.1.4 addRoundKey() (equation 5.9)
addRoundKey ∷ StateType alg → RoundWType alg → StateType alg
addRoundKey = zipWith (zipWith (⊕))

-- | 5.3.1 invShiftRows() (equation 5.5)
invShiftRows ∷ StateType alg → StateType alg
invShiftRows state = transpose (zipWith rotateRight (transpose state) (iterateI (+1) (0 ∷ Integer)))

-- | 5.3.2 invSubBytes() implemented with table 6
invSubBytes ∷ StateType alg → StateType alg
invSubBytes = map (map (sBox xyInvSBox))

-- | 5.3.3 the inverse of mixColumns() (equation5.14, 5.15)
invMixColumns ∷ StateType alg → StateType alg
invMixColumns = fmap (vectorMatrixMultiplication aInvMixColumns)

-- | 5.3.4 invAddRoundKey() (equation 5.9)
invAddRoundKey ∷ StateType alg → RoundWType alg → StateType alg
invAddRoundKey = addRoundKey

--------------------------------------------------------------------------------------
-- Section 5.2 and 5.3: keyexpansion support functions                              --
--------------------------------------------------------------------------------------
rotWord ∷ WordType alg → WordType alg
rotWord word = rotateLeft word (1 ∷ Integer)

subWord ∷ WordType alg → WordType alg
subWord = map (sBox xySBox)

xorWord ∷ WordType alg → WordType alg → WordType alg
xorWord = zipWith (⊕)


-- 5.2 table 5
class AESConstants (alg ∷ AES) where
  _Rcon ∷ Proxy alg → RconType alg
  _Rcon¹ ∷ Proxy alg → WordType alg

instance AESConstants AES128 where
    _Rcon¹ _ = 0x01:>0x00:>0x00:>0x00:>Nil
    _Rcon alg = transpose (fmap (generateI xTimes) (_Rcon¹ alg))
deriving via AES128 instance AESConstants AES192
deriving via AES128 instance AESConstants AES256



