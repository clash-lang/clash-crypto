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
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}

module Clash.Crypto.Cipher.AES.Specification.Definitions where


import Clash.Prelude(d4, Vec(..), KnownNat(..),Bits(..), Bit(..), Unsigned(..),resize,   (.<<+), xor, Nat(..), divSNat )
import Clash.Sized.Internal.BitVector(BitVector(..), bitPattern, xor#, eq#)
import Clash.Sized.Vector(iterateI, splitAtI, scanl, dropI,takeI, map, concat, foldl, last,(+>>), zipWith, mapAccumL, rotateRight,rotateLeft, generateI, transpose,unconcatBitVector#, bv2v, v2bv, unconcatI, (++), (!!))
import GHC.Internal.Bits

import Control.Arrow (first)
import Data.Proxy (Proxy)
import Data.Type.Bool (If)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Cipher.AES.Specification.Types
import Clash.Crypto.Cipher.AES.Specification.Constants
import Clash.Sized.Vector.Extra ((‼))
import GHC.Show (Show)
import GHC.TypeNats (Nat)
import GHC.Generics (Generic)
import GHC.TypeLits
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
(⊕) = xor#
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
(•) b c = Clash.Sized.Vector.foldl (⊕) (0x00) (Clash.Sized.Vector.zipWith (\f g →  if f then g else (0x00)) (bv2vbool b) (list_xtimes c))
    where
        list_xtimes ∷  (KnownNat n, KnownNat w) ⇒ BitVector w → Vec n (BitVector w)
        list_xtimes = iterateI xTimes
        -- | function that transform from bitvector to vector of booleans.
        bv2vbool ∷  (KnownNat w) ⇒ BitVector w → Vec w Bool
        bv2vbool b = fmap (testBit b) (iterateI (+1) 0)



-- | Section 4.3: Multiplication of Words by a Fixed Matrix in GF(2⁸)
-- | Generic multiplication
matrixMultiplication ∷ (KnownNat w, KnownNat m, KnownNat n) ⇒ Vec m (Vec n (BitVector w)) → Vec n (BitVector w) → Vec m (BitVector w)
matrixMultiplication a b = fmap (vectorMultiplication b) a
    where
        vectorMultiplication ∷ (KnownNat w, KnownNat n) ⇒  Vec n (BitVector w) → Vec n (BitVector w) → BitVector w
        vectorMultiplication b a = Clash.Sized.Vector.foldl (⊕) 0x00  (Clash.Sized.Vector.zipWith (•) b a)

-- | Multiplication as defined in equation 4.9
-- | Matrix multiplication based on two vectors as neded MixColumns() and InvMixColumns()
vectorMatrixMultiplication :: (KnownNat w, KnownNat n) => Vec n (BitVector w) -> Vec n (BitVector w) -> Vec n (BitVector w)
vectorMatrixMultiplication a = matrixMultiplication (generateMatrixA a)
    where
        generateMatrixA :: (KnownNat w, KnownNat n) =>  Vec n (BitVector w) -> Vec n (Vec n (BitVector w))
        generateMatrixA a = transpose (iterateI (`Clash.Sized.Vector.rotateRight` 1) a)

-- | Section 4.3:
-- | inverse based of 4.11
inv :: (KnownNat w) =>
     BitVector w -> BitVector w
inv b = Clash.Sized.Vector.foldl (•) 0X01 (list_binary_powers b)
    where
        pow2 :: KnownNat w => BitVector w -> BitVector w
        pow2 b = (•) b b
        list_binary_powers :: (KnownNat w) => BitVector w -> Vec w (BitVector w)
        list_binary_powers = Clash.Sized.Vector.generateI pow2
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
-- test matrix:
testMatrix ∷ StateType alg
testMatrix = (0x00 :> 0x10 :> 0x20 :> 0x30 :> Nil) :> (0x01 :> 0x11 :> 0x21 :> 0x31 :> Nil) :> (0x02 :> 0x12 :> 0x22 :> 0x32 :> Nil) :> (0x03 :> 0x13 :> 0x23 :> 0x33 :> Nil) :>Nil
-- Shift test 
-- Clash.Crypto.Cipher.AES.Specification.Definitions.invShiftRows ( Clash.Crypto.Cipher.AES.Specification.Definitions.shiftRows Clash.Crypto.Cipher.AES.Specification.Definitions.test_matrix)
-- should give the same back.
-- Similiar for mixcolumns
--  Clash.Crypto.Cipher.AES.Specification.Definitions.invMixColumns ( Clash.Crypto.Cipher.AES.Specification.Definitions.mixColumns Clash.Crypto.Cipher.AES.Specification.Definitions.test_matrix)

-- | 5.1.1 subBytes() (equation 5.2, 5.3, 5.4) but implemented with table 4
subBytes ∷ StateType alg → StateType alg
subBytes = Clash.Sized.Vector.map (Clash.Sized.Vector.map (sBox xySBox))
-- | the methode to select the right value from sBox that is given with it. 
sBox ∷ Vec (2 GHC.TypeLits.* ByteSize alg) (Vec (2 GHC.TypeLits.* ByteSize alg) (ByteType alg)) → ByteType alg → ByteType alg
sBox m a = (m Clash.Sized.Vector.!! x_part a 0)  Clash.Sized.Vector.!! x_part a 1
    where
        splitBitVector ∷ ByteType alg → SplitByteType alg -- Binding such that the rest also works.
        splitBitVector = unconcatBitVector#
        x_part ∷ (Enum i) ⇒ ByteType alg → i → NibbleType alg
        x_part b c = splitBitVector b Clash.Sized.Vector.!! c

-- | 5.1.2 shiftRows() (equation 5.5)
shiftRows ∷ StateType alg → StateType alg
shiftRows state = transpose (Clash.Sized.Vector.zipWith Clash.Sized.Vector.rotateLeft (transpose state) (iterateI (+1) 0))

-- | 5.1.3 mixColumns() (equation 5.7, 5.8)
mixColumns ∷ StateType alg → StateType alg
mixColumns = fmap (vectorMatrixMultiplication aMixColumns)

-- | 5.1.4 addRoundKey() (equation 5.9)
addRoundKey ∷ StateType alg → RoundWType alg → StateType alg
addRoundKey = Clash.Sized.Vector.zipWith (Clash.Sized.Vector.zipWith (⊕))

-- | 5.3.1 invShiftRows() (equation 5.5)
invShiftRows ∷ StateType alg → StateType alg
invShiftRows state = transpose (Clash.Sized.Vector.zipWith Clash.Sized.Vector.rotateRight (transpose state) (iterateI (+1) 0))

-- | 5.3.2 invSubBytes() implemented with table 6
invSubBytes ∷ StateType alg → StateType alg
invSubBytes = Clash.Sized.Vector.map (Clash.Sized.Vector.map (sBox xySBox))

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
rotWord word = Clash.Sized.Vector.rotateLeft word 1

subWord ∷ WordType alg → WordType alg
subWord = Clash.Sized.Vector.map (sBox xySBox)

xorWord ∷ WordType alg → WordType alg → WordType alg
xorWord = Clash.Sized.Vector.zipWith (⊕)
-- 5.2 table 5
class AESConstants (alg ∷ AES) where
  _Rcon ∷ Proxy alg → RconType alg
  _Rcon¹ ∷ Proxy alg → WordType alg

instance AESConstants AES128 where
    _Rcon¹ _ = 0x01:>0x00:>0x00:>0x00:>Nil
    _Rcon alg = transpose (fmap (Clash.Sized.Vector.generateI xTimes) (_Rcon¹ alg))
deriving via AES128 instance AESConstants AES192
deriving via AES128 instance AESConstants AES256

-- | Implementation of 
class AESFunctions (alg ∷ AES) where
  keyExpansion ∷ Proxy alg →  KeyType alg → WType alg --WType alg

instance AESFunctions AES128 where
-- The keyexpansion function as written in Algorithm 2 and as illustrate in 6
--  keys 
-- k1 = wl    ==> formula(wl⊹3) ⊕ wl    ==> wl⊹4   
-- k2 = wl⊹1  ==> wl            ⊕ wl⊹1  ==> wl⊹5   
-- k3 = wl⊹2  ==> wl⊹1          ⊕ wl⊹2  ==> wl⊹6
-- k4 = wl⊹3  ==> wl⊹2          ⊕ wl⊹3  ==> wl⊹7
    keyExpansion ∷ Proxy AES128 → KeyType AES128 → WType AES128
    keyExpansion alg key = Clash.Sized.Vector.concat (Clash.Sized.Vector.scanl (middelCalculation alg) key (Clash.Sized.Vector.iterateI (+1) 0))
        where
        middelCalculation ∷ Enum i ⇒ Proxy AES128 → KeyType AES128→ i → KeyType AES128
        middelCalculation alg ws i = Clash.Sized.Vector.zipWith xorWord ((+>>) (partWord ws i) ws) ws
                where
                    partWord ws index = xorWord (subWord (rotWord (Clash.Sized.Vector.last ws)))   (_Rcon alg Clash.Sized.Vector.!! index)


instance AESFunctions AES192 where
    -- Similiar fashion as for AES128
    -- The keyexpansion function as written in Algorithm 2 and as illustrate in 7
    keyExpansion ∷ Proxy AES192 → KeyType AES192 → WType AES192
    keyExpansion alg key = takeI (keyExpansionInBlocks alg key)
        where 
            keyExpansionInBlocks ∷ Proxy AES192 → KeyType AES192 → Vec (Nk AES192 GHC.TypeLits.* Nr AES192) (WordType AES192)
            keyExpansionInBlocks alg key = Clash.Sized.Vector.concat (Clash.Sized.Vector.scanl (middelCalculation alg) key (Clash.Sized.Vector.iterateI (+1) 1))
                where
                middelCalculation ∷ Enum i ⇒ Proxy AES192 → KeyType AES192 → i → KeyType AES192
                middelCalculation alg ws i = Clash.Sized.Vector.zipWith xorWord ((+>>) (partWord ws i) ws) ws
                        where
                            partWord ws index = xorWord (subWord (rotWord (Clash.Sized.Vector.last ws)))   (_Rcon alg Clash.Sized.Vector.!! index)

instance AESFunctions AES256 where
    -- The keyexpansion function as written in Algorithm 2 and as illustrate in 8
    keyExpansion ∷ Proxy AES256 → KeyType AES256 → WType AES256
    keyExpansion alg key = takeI (keyExpansionInBlocks alg key)
        where 
            keyExpansionInBlocks ∷ Proxy AES256 → KeyType AES256 → Vec (Nk AES256 GHC.TypeLits.* (Nr AES256 + 3) GHC.TypeLits.* (Nr AES256 + 3)) (WordType AES256)
            keyExpansionInBlocks alg key = Clash.Sized.Vector.concat (Clash.Sized.Vector.scanl (middelCalculation alg) key (Clash.Sized.Vector.iterateI (+1) 1))
                where
                middelCalculation ∷ Enum i ⇒ Proxy AES256 → KeyType AES256 → i → KeyType AES256
                middelCalculation alg ws i = firstPart ws i Clash.Sized.Vector.++ secondPart ws i
                    where
                        firstPart ws i = Clash.Sized.Vector.zipWith xorWord ((+>>) (partWord (firstSplit ws) i) (firstSplit ws)) (firstSplit ws)
                        firstSplit = Clash.Sized.Vector.takeI @(Nk AES256 `Div` 2)
                        secondPart ws i= Clash.Sized.Vector.zipWith xorWord ((+>>) (subWord (Clash.Sized.Vector.last (firstPart ws i))) (secondSplit ws)) (secondSplit ws)
                        secondSplit = Clash.Sized.Vector.dropI @(Nk AES256 `Div` 2)
                        partWord ws index = xorWord (subWord (rotWord (Clash.Sized.Vector.last ws)))   (_Rcon alg Clash.Sized.Vector.!! index)



