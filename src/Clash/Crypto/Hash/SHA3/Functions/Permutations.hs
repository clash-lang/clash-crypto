{-|
Module      : Clash.Crypto.Hash.SHA3.Functions.Permutations
Copyright   : Copyright © 2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

This modules contains the implementations of the
Keccak-p[b, nᵣ] and Keccak-f[b] families of permutations.
-}
{-# LANGUAGE MagicHash #-}

module Clash.Crypto.Hash.SHA3.Functions.Permutations
  ( reverseBitsInByte, reverseBitsInBytes
  , trunc, truncLT
  , theta, θ
  , rho, ρ
  , pi, π
  , chi, χ
  , rcRecursive, rcRom, rc, rcVecs
  , iota, ι
  , iotal6nr24, ιl6nr24
  , rnd, rnd6
  , keccakp
  , keccakf) where

import Clash.Prelude.Safe hiding (pi, type (^))
import Clash.Sized.Internal.BitVector (replaceBit#)
import Clash.Class.NumConvert (numConvert)

import Language.Haskell.Unicode (type (≤))
import GHC.TypeNats.Proof (Rewrite(Rewrite), type (<), QED (using))

import Data.Constraint.Nat.Extra (LtImpliesLE, CancelMultiple)
import Clash.Crypto.Hash.SHA3.State
    ( KnownStateL
    , StateWidth
    , StateArray
    , State
    , toArray
    , toState
    )

-- | A util function for looping over
-- a BitVector of length m n times.
forI ∷
  ∀ (n ∷ Nat). (KnownNat n) ⇒
  ∀ (m ∷ Nat). (KnownNat m) ⇒
  BitVector m →
  -- ^ The input vector.
  (BitVector m → Index n → BitVector m) →
  -- ^ The function that updates the vector on every iteration.
  BitVector m
forI v f  =  foldl f v (indicesI ∷ Vec n (Index n))

-- TODO: This is known to have slow simulation implementation.
-- https://github.com/clash-lang/clash-compiler/issues/2725
-- We should update once the issue is fixed.
-- | A function to reverse the order of the bits of a BitVector.
reverseBitsInByte ∷ KnownNat n ⇒ BitVector n → BitVector n
reverseBitsInByte = v2bv . reverse . bv2v

-- | A function that:
--
-- * splits a BitVector into a Vec of bytes.
-- * reverses the order of the bits inside each byte.
-- * packs the result to a @BitPack a@.
reverseBitsInBytes ∷
  ∀ (n ∷ Nat). (KnownNat n, n `Mod` 8 ~ 0) ⇒
  ∀ a. (BitPack a, BitSize a ~ n) ⇒
  BitVector n →
  a
reverseBitsInBytes
  | Rewrite ← using @(CancelMultiple n 8)
  = bitCoerce . map (reverse @8 @(BitVector 1)) . unpack

-- Truncation utility functions

-- | A truncation utility function that returns
-- the @r@ left-most bits of a @BitVector b@,
-- where @r ≤ b@.
trunc ∷
  ∀ (b ∷ Nat).  KnownNat b ⇒
  ∀ (r ∷ Nat) → (KnownNat r, 1 ≤ r, r <= b) ⇒
  BitVector b →
  BitVector r
trunc r input
  = let (tr ∷ BitVector r, _ ∷ BitVector (b - r)) = split input
    in tr

-- | A truncation utility function that returns
-- the @r@ left-most bits of a @BitVector b@,
-- where @r < b@.
truncLT ∷
  ∀ (b ∷ Nat).  KnownNat b ⇒
  ∀ (r ∷ Nat) → (KnownNat r, 1 ≤ r, r < b) ⇒
  BitVector b →
  BitVector r
truncLT r input
  | Rewrite ← using @(LtImpliesLE r b)
  = trunc r input

-- | Implementation of the theta step mapping
--  as defined in FIPS-202.
theta, θ ∷
  ∀ (l ∷ Nat). KnownStateL l ⇒
  State l →
  State l
θ = theta
theta state = imap (\x sheet → map (xorLane x) sheet) state
 where
  parities = map (foldl1 xor) state
  c2 = map (`rotateR` 1) parities
  xorLane x lane =    lane
                `xor` parities !! satPred SatWrap x
                `xor` c2 !! satSucc SatWrap x

-- | Implementation of the rho step mapping
--  as defined in FIPS-202.
rho, ρ ∷
  ∀ (l ∷ Nat). KnownStateL l ⇒
  State l →
  State l
ρ = rho
rho state = foldl nextA state vecXYs
 where
  nextXY ∷ (Index 5, Index 5) → Index 24 → ((Index 5, Index 5), (Index 5, Index 5, Int))
  nextXY (x, y) tidx =
    let x' = y
        y' = satAdd SatWrap (satMul SatWrap 2 x) (satMul SatWrap 3 y)
        t = numConvert tidx
        t' = (((t + 1) * (t + 2)) `div` 2) `mod` natToNum @(StateWidth l)
    in ((x', y'), (x, y, t'))

  vecXYs ∷ Vec 24 (Index 5, Index 5, Int)
  vecXYs = snd $ mapAccumL nextXY (1, 0) (indicesI ∷ Vec 24 (Index 24))

  nextA s (x, y, t) =
    let lane' = rotateR (s !! x !! y) t
        sheet' = replace y lane' (s !! x)
    in replace x sheet' s

-- | Implementation of the rho step mapping optimized for @l = 6@
--  as defined in FIPS-202.
rho6, ρ6 ∷
  State 6 →
  State 6
ρ6 = rho6
rho6 state = zipWith (zipWith rotateR) state rotations
 where
  rotations =
    (0 :> 36 :> 3 :> 41 :> 18 :> Nil) :>
    (1 :> 44 :> 10 :> 45 :> 2 :> Nil) :>
    (62 :> 6 :> 43 :> 15 :> 61 :> Nil) :>
    (28 :> 55 :> 25 :> 21 :> 56 :> Nil) :>
    (27 :> 20 :> 39 :> 8 :> 14 :> Nil) :> Nil

-- | Implementation of the pi step mapping
--  as defined in FIPS-202.
pi, π ∷
  ∀ (l ∷ Nat). KnownStateL l ⇒
  State l →
  State l
π = pi
pi state =
  imap (\x sheet →
    imap (\y _ → rotateLanes x y) sheet) state
 where
  rotateLanes x y =
    let x' = satAdd SatWrap x (satMul SatWrap 3 y)
    in state !! x' !! x

-- | Implementation of the chi step mapping
--  as defined in FIPS-202.
chi, χ ∷
  ∀ (l ∷ Nat). KnownStateL l ⇒
  State l →
  State l
χ = chi
chi state = map unconcatBitVector# $
  imap nonLinear rows
 where
  rows = map concatBitVector# state
  nonLinear x row =
    let x1 = satAdd SatWrap x 1
        x2 = satAdd SatWrap x 2
    in row `xor` ((rows !! x1 `xor` oneBits) .&. rows !! x2)

-- | A recursive implementation of the rc function.
rcRecursive ∷
  Index 255 →
  Bit
rcRecursive 0 = high
rcRecursive t =
  let initR = 0b10_000_000 ∷ BitVector 8
      loop i r | i == t = r
      loop i r =
        let r1 = (0b0 ∷ BitVector 1) ++# r
            r2 = replaceBit (8 - 0 ∷ Index 9)
                    (r1 ! (8 - 0 ∷ Index 9) `xor` r1 ! (8 - 8 ∷ Index 9)) r1
            r3 = replaceBit (8 - 4 ∷ Index 9)
                    (r2 ! (8 - 4 ∷ Index 9) `xor` r2 ! (8 - 8 ∷ Index 9)) r2
            r4 = replaceBit (8 - 5 ∷ Index 9)
                    (r3 ! (8 - 5 ∷ Index 9) `xor` r3 ! (8 - 8 ∷ Index 9)) r3 
            r5 = replaceBit (8 - 6 ∷ Index 9)
                    (r4 ! (8 - 6 ∷ Index 9) `xor` r4 ! (8 - 8 ∷ Index 9)) r4 
        in loop (i + 1) (trunc 8 r5)
  in lsb $ loop 1 initR

-- | A BitVector holding all the precomputed values for rc.
rcRom ∷ BitVector 256
rcRom = 0x8E25C0C93720ADACB0FB7AE886C79CC5A452A7767BF4CD460EABE509FE178D01

-- | A util to read from the rcRom.
rc ∷ Index 256 → Bit
rc i = rcRom ! i

-- | Implementation of the computation of the RC vector for l and nr.
rcVecs ∷
  ∀ (l ∷ Nat) (nr ∷ Nat). (KnownStateL l, KnownNat nr, nr <= 256) ⇒
  Vec nr (BitVector (StateWidth l))
rcVecs = unfoldrI f minBound
 where
  f ∷ Index nr → (BitVector (StateWidth l), Index nr)
  f i =
    let
      ir = natToNum @(12 + 2 * l) - natToNum @nr + numConvert i ∷ Index 256
      initRC = zeroBits ∷ BitVector (StateWidth l)
      finalRC = forI @(l + 1) @(StateWidth l) initRC
        (\vec j →
          let idx = shiftL 1 (fromEnum j) - 1    -- 2 ^ j - 1
              rcBit = rc (numConvert j + 7 * ir) -- rc(j + 7 * ir)
          in replaceBit# vec (natToNum @(StateWidth l) - 1 - idx) rcBit
        )
    in (finalRC, i + 1)

-- | Precomputed RC vectors for @l = 6@ and @nr = 24@.
rcVecsl6nr24 ∷ Vec 24 (BitVector 64)
rcVecsl6nr24 =
     0x8000_0000_0000_0000 :> 0x4101_0000_0000_0000
  :> 0x5101_0000_0000_0001 :> 0x0001_0001_0000_0001
  :> 0xd101_0000_0000_0000 :> 0x8000_0001_0000_0000
  :> 0x8101_0001_0000_0001 :> 0x9001_0000_0000_0001
  :> 0x5100_0000_0000_0000 :> 0x1100_0000_0000_0000
  :> 0x9001_0001_0000_0000 :> 0x5000_0001_0000_0000
  :> 0xd101_0001_0000_0000 :> 0xd100_0000_0000_0001
  :> 0x9101_0000_0000_0001 :> 0xc001_0000_0000_0001
  :> 0x4001_0000_0000_0001 :> 0x0100_0000_0000_0001
  :> 0x5001_0000_0000_0000 :> 0x5000_0001_0000_0001
  :> 0x8101_0001_0000_0001 :> 0x0101_0000_0000_0001
  :> 0x8000_0001_0000_0000 :> 0x1001_0001_0000_0001
  :> Nil

-- | Implementation of the iota step mapping
--  as defined in FIPS-202.
iota, ι ∷
  ∀ (l ∷ Nat) (nr ∷ Nat). (KnownStateL l, KnownNat nr, nr <= 256) ⇒
  State l →
  Index nr →
  State l
ι = iota
iota ((l :> lanes) :> rows) ir = ((l `xor` (rcVecs @l @nr !! ir)) :> lanes) :> rows

-- | Implementation of the iota step mapping optimized for @l = 6@
--  and @nr = 24@ as defined in FIPS-202.
iotal6nr24, ιl6nr24 ∷
  State 6 →
  Index 24 →
  State 6
ιl6nr24 = iotal6nr24
iotal6nr24 ((l :> lanes) :> rows) ir = ((l `xor` (rcVecsl6nr24 !! ir)) :> lanes) :> rows

-- | Implementation of the round permutation.
rnd ∷
  ∀ (l ∷ Nat). KnownStateL l ⇒
  ∀ (nr ∷ Nat). (KnownNat nr, nr <= 256) ⇒
  State l →
  Index nr →
  State l
rnd = ι . χ . π . ρ . θ

-- | Implementation of the round permutation for @l = 6@ using
-- precompted values wherever possible.
rnd6 ∷
  State 6 →
  Index 24 →
  State 6
rnd6 = ι . χ . π . ρ6 . θ

-- | Implementation of the Keccak-p[b, nᵣ]
--  families of permutations as defined in FIPS-202.
keccakp ∷
  ∀ (l ∷ Nat). KnownStateL l ⇒
  ∀ (nr ∷ Nat) → (KnownNat nr, 1 <= nr, nr <= 256) ⇒
  StateArray l →
  StateArray l
keccakp nr state = toArray $ foldl rnd (toState state) (indicesI @nr)

-- | Implementation of the Keccak-f[b]
--  families of permutations as defined in FIPS-202.
keccakf ∷
  ∀ (l ∷ Nat). KnownStateL l ⇒
  StateArray l →
  StateArray l
keccakf state = keccakp (type (12 + 2 * l)) state
