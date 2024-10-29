{-|
Module      : Clash.Crypto.Hash.SHA.Specification.Definitions
Copyright   : Copyright © 2024 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Basic definitions covering the fundamentals of FIPS 180-4.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}

module Clash.Crypto.Hash.SHA.Specification.Definitions where

import Clash.Prelude
import Clash.Sized.Internal.BitVector

import Data.Constraint (Dict(..))
import Data.Constraint.Nat.Extra (leTrans)
import Data.Proxy (Proxy)
import Data.Type.Bool (If)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Hash.SHA.Specification.Types

-------------------------------------------
-- Section 2.2.2: Symbols and Operations --
-------------------------------------------

infixl 8 ∧
(∧) ∷ KnownNat w ⇒ BitVector w → BitVector w → BitVector w
(∧) = and#

infixl 5 ∨
(∨) ∷ KnownNat w ⇒ BitVector w → BitVector w → BitVector w
(∨) = or#

infixl 6 ⊕
(⊕) ∷ KnownNat w ⇒ BitVector w → BitVector w → BitVector w
(⊕) = xor#

(¬) ∷ KnownNat w ⇒ BitVector w → BitVector w
(¬) = complement#

infixl 5 ≪
(≪) ∷ (KnownNat w, n ≤ w) ⇒ BitVector w → SNat n → BitVector w
x ≪ n = shiftL# x $ snatToNum n

infixl 5 ≫
(≫) ∷ (KnownNat w, n ≤ w) ⇒ BitVector w → SNat n → BitVector w
x ≫ n = shiftR# x $ snatToNum n

_ROTL ∷ ∀ n w. (KnownNat w, n ≤ w) ⇒ SNat n → BitVector w → BitVector w
_ROTL SNat x = (x ≪ SNat @n) ∨ (x ≫ SNat @(w - n))

_ROTR ∷ ∀ n w. (KnownNat w, n ≤ w) ⇒ SNat n → BitVector w → BitVector w
_ROTR SNat x = (x ≫ SNat @n) ∨ (x ≪ SNat @(w - n))

-- TODO: prove that
--   ROTL (SNat @n) x ≡ ROTR (SNat @(w - n)) x
--   ROTR (SNat @n) x ≡ ROTL (SNat @(w - n)) x

_SHR ∷ ∀ n w. (KnownNat w, n ≤ w) ⇒ SNat n → BitVector w → BitVector w
_SHR n x = x ≫ n

----------------------------
-- Section 4.1: Functions --
----------------------------

_Ch ∷ KnownNat w ⇒ BitVector w → BitVector w → BitVector w → BitVector w
_Ch x y z = (x ∧ y) ⊕ ((¬) x ∧ z)

_Parity ∷ KnownNat w ⇒ BitVector w → BitVector w → BitVector w → BitVector w
_Parity x y z = x ⊕ y ⊕ z

_Mai ∷ KnownNat w ⇒ BitVector w → BitVector w → BitVector w → BitVector w
_Mai x y z = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)

_f ∷ t ≤ 79 ⇒ SNat t → BitVector 32 → BitVector 32 → BitVector 32 → BitVector 32
_f t
  | SNatLE ← compareSNat t (SNat @19) = _Ch
  | SNatLE ← compareSNat t (SNat @39) = _Parity
  | SNatLE ← compareSNat t (SNat @59) = _Mai
  | otherwise                         = _Parity

-- | All algorithms define some functions Σ₀, Σ₁, σ₀, and σ₁, which
-- are different for each algorithm. We use the 'SHAFunctions' class
-- to capture the differences among the 'SHA' instances.
class SHAFunctions (alg ∷ SHA) where
  _Σ₀ ∷ Proxy alg → SHAWord alg → SHAWord alg
  _Σ₁ ∷ Proxy alg → SHAWord alg → SHAWord alg
  _σ₀ ∷ Proxy alg → SHAWord alg → SHAWord alg
  _σ₁ ∷ Proxy alg → SHAWord alg → SHAWord alg

instance SHAFunctions SHA224 where
  _Σ₀ _ x = _ROTR  @2 SNat x ⊕ _ROTR @13 SNat x ⊕ _ROTR @22 SNat x
  _Σ₁ _ x = _ROTR  @6 SNat x ⊕ _ROTR @11 SNat x ⊕ _ROTR @25 SNat x
  _σ₀ _ x = _ROTR  @7 SNat x ⊕ _ROTR @18 SNat x ⊕ _SHR   @3 SNat x
  _σ₁ _ x = _ROTR @17 SNat x ⊕ _ROTR @19 SNat x ⊕ _SHR  @10 SNat x

deriving via SHA224 instance SHAFunctions SHA256

instance SHAFunctions SHA384 where
  _Σ₀ _ x = _ROTR @28 SNat x ⊕ _ROTR @34 SNat x ⊕ _ROTR @39 SNat x
  _Σ₁ _ x = _ROTR @14 SNat x ⊕ _ROTR @18 SNat x ⊕ _ROTR @41 SNat x
  _σ₀ _ x = _ROTR  @1 SNat x ⊕ _ROTR  @8 SNat x ⊕ _SHR   @7 SNat x
  _σ₁ _ x = _ROTR @19 SNat x ⊕ _ROTR @61 SNat x ⊕ _SHR   @6 SNat x

deriving via SHA384 instance SHAFunctions SHA512
deriving via SHA384 instance SHAFunctions SHA512224
deriving via SHA384 instance SHAFunctions SHA512256

----------------------------
-- Section 4.2: Constants --
----------------------------

-- | All algorithms define some constants @K@, which are different for
-- each algorithm. We use the 'SHAConstants' class to capture the
-- differences among the 'SHA' instances.
class SHAConstants (alg ∷ SHA) where
  type MaxIndex alg ∷ Nat
  _K ∷ Proxy alg → ∀ t. t ≤ MaxIndex alg ⇒ SNat t → SHAWord alg

instance SHAConstants SHA1 where
  type MaxIndex SHA1 = 79
  _K _ t
    | SNatLE ← compareSNat t (SNat @19) = 0x5a827999
    | SNatLE ← compareSNat t (SNat @39) = 0x6ed9eba1
    | SNatLE ← compareSNat t (SNat @59) = 0x8f1bbcdc
    | otherwise                         = 0xca62c1d6

instance SHAConstants SHA224 where
  type MaxIndex SHA224 = 63
  _K _ (SNat ∷ SNat t) = at @t @(MaxIndex SHA224 - t) SNat v
   where
    v ∷ Vec (MaxIndex SHA224 + 1) (SHAWord SHA224)
    v = 0x428a2f98 :> 0x71374491 :> 0xb5c0fbcf :> 0xe9b5dba5 :> 0x3956c25b
     :> 0x59f111f1 :> 0x923f82a4 :> 0xab1c5ed5 :> 0xd807aa98 :> 0x12835b01
     :> 0x243185be :> 0x550c7dc3 :> 0x72be5d74 :> 0x80deb1fe :> 0x9bdc06a7
     :> 0xc19bf174 :> 0xe49b69c1 :> 0xefbe4786 :> 0x0fc19dc6 :> 0x240ca1cc
     :> 0x2de92c6f :> 0x4a7484aa :> 0x5cb0a9dc :> 0x76f988da :> 0x983e5152
     :> 0xa831c66d :> 0xb00327c8 :> 0xbf597fc7 :> 0xc6e00bf3 :> 0xd5a79147
     :> 0x06ca6351 :> 0x14292967 :> 0x27b70a85 :> 0x2e1b2138 :> 0x4d2c6dfc
     :> 0x53380d13 :> 0x650a7354 :> 0x766a0abb :> 0x81c2c92e :> 0x92722c85
     :> 0xa2bfe8a1 :> 0xa81a664b :> 0xc24b8b70 :> 0xc76c51a3 :> 0xd192e819
     :> 0xd6990624 :> 0xf40e3585 :> 0x106aa070 :> 0x19a4c116 :> 0x1e376c08
     :> 0x2748774c :> 0x34b0bcb5 :> 0x391c0cb3 :> 0x4ed8aa4a :> 0x5b9cca4f
     :> 0x682e6ff3 :> 0x748f82ee :> 0x78a5636f :> 0x84c87814 :> 0x8cc70208
     :> 0x90befffa :> 0xa4506ceb :> 0xbef9a3f7 :> 0xc67178f2 :> Nil

deriving via SHA224 instance SHAConstants SHA256

instance SHAConstants SHA384 where
  type MaxIndex SHA384 = 79
  _K _ (SNat ∷ SNat t) = at @t @(MaxIndex SHA384 - t) SNat v
   where
    v ∷ Vec (MaxIndex SHA384 + 1) (SHAWord SHA384)
    v = 0x428a2f98d728ae22 :> 0x7137449123ef65cd :> 0xb5c0fbcfec4d3b2f
     :> 0xe9b5dba58189dbbc :> 0x3956c25bf348b538 :> 0x59f111f1b605d019
     :> 0x923f82a4af194f9b :> 0xab1c5ed5da6d8118 :> 0xd807aa98a3030242
     :> 0x12835b0145706fbe :> 0x243185be4ee4b28c :> 0x550c7dc3d5ffb4e2
     :> 0x72be5d74f27b896f :> 0x80deb1fe3b1696b1 :> 0x9bdc06a725c71235
     :> 0xc19bf174cf692694 :> 0xe49b69c19ef14ad2 :> 0xefbe4786384f25e3
     :> 0x0fc19dc68b8cd5b5 :> 0x240ca1cc77ac9c65 :> 0x2de92c6f592b0275
     :> 0x4a7484aa6ea6e483 :> 0x5cb0a9dcbd41fbd4 :> 0x76f988da831153b5
     :> 0x983e5152ee66dfab :> 0xa831c66d2db43210 :> 0xb00327c898fb213f
     :> 0xbf597fc7beef0ee4 :> 0xc6e00bf33da88fc2 :> 0xd5a79147930aa725
     :> 0x06ca6351e003826f :> 0x142929670a0e6e70 :> 0x27b70a8546d22ffc
     :> 0x2e1b21385c26c926 :> 0x4d2c6dfc5ac42aed :> 0x53380d139d95b3df
     :> 0x650a73548baf63de :> 0x766a0abb3c77b2a8 :> 0x81c2c92e47edaee6
     :> 0x92722c851482353b :> 0xa2bfe8a14cf10364 :> 0xa81a664bbc423001
     :> 0xc24b8b70d0f89791 :> 0xc76c51a30654be30 :> 0xd192e819d6ef5218
     :> 0xd69906245565a910 :> 0xf40e35855771202a :> 0x106aa07032bbd1b8
     :> 0x19a4c116b8d2d0c8 :> 0x1e376c085141ab53 :> 0x2748774cdf8eeb99
     :> 0x34b0bcb5e19b48a8 :> 0x391c0cb3c5c95a63 :> 0x4ed8aa4ae3418acb
     :> 0x5b9cca4f7763e373 :> 0x682e6ff3d6b2b8a3 :> 0x748f82ee5defb2fc
     :> 0x78a5636f43172f60 :> 0x84c87814a1f0ab72 :> 0x8cc702081a6439ec
     :> 0x90befffa23631e28 :> 0xa4506cebde82bde9 :> 0xbef9a3f7b2c67915
     :> 0xc67178f2e372532b :> 0xca273eceea26619c :> 0xd186b8c721c0c207
     :> 0xeada7dd6cde0eb1e :> 0xf57d4f7fee6ed178 :> 0x06f067aa72176fba
     :> 0x0a637dc5a2c898a6 :> 0x113f9804bef90dae :> 0x1b710b35131c471b
     :> 0x28db77f523047d84 :> 0x32caab7b40c72493 :> 0x3c9ebe0a15c9bebc
     :> 0x431d67c49c100d4c :> 0x4cc5d4becb3e42b6 :> 0x597f299cfc657e2a
     :> 0x5fcb6fab3ad6faec :> 0x6c44198c4a475817 :> Nil

deriving via SHA384 instance SHAConstants SHA512
deriving via SHA384 instance SHAConstants SHA512224
deriving via SHA384 instance SHAConstants SHA512256

--------------------------------------
-- Section 5.1: Padding the Message --
--------------------------------------

-- | The number of bits required to store the size of a message at the
-- end of the padding.
type SizeBits alg = 2 * WordSize alg

-- | The number of "zero" bits that must added in between the message
-- plus the '1' bit and it's size stored at the end of the padding.
type PaddingZeros ∷ SHA → Nat → Nat
type family PaddingZeros alg ℓ where
  PaddingZeros alg ℓ =
    RequiredBlocks alg ℓ * BlockSize alg
      - ℓ `Mod` BlockSize alg
      - 1
      - SizeBits alg

-- | The number of bits of a padded message.
type PaddedMsgBits (alg ∷ SHA) (ℓ ∷ Nat) =
  ℓ + 1 + PaddingZeros alg ℓ + SizeBits alg

-- | The number of message blocks required to store the padding.
type RequiredBlocks (alg ∷ SHA) (ℓ ∷ Nat) =
  If (1 + SizeBits alg <=? BlockSize alg - ℓ `Mod` BlockSize alg) 1 2

-------------------------------------------------
-- Section 5.3: Setting the Initial Hash Value --
-------------------------------------------------

-- | All algorithms define an initial hash value H⁰, which is different
-- for each algorithm. We use the 'SHAInitials' class to capture the
-- differences among the 'SHA' instances.
class SHAInitials (alg ∷ SHA) where
  _H⁰ ∷ Proxy alg → HashValue alg

instance SHAInitials SHA1 where
  _H⁰ _ = 0x67452301
       :> 0xefcdab89
       :> 0x98badcfe
       :> 0x10325476
       :> 0xc3d2e1f0
       :> Nil

instance SHAInitials SHA224 where
  _H⁰ _ = 0xc1059ed8
       :> 0x367cd507
       :> 0x3070dd17
       :> 0xf70e5939
       :> 0xffc00b31
       :> 0x68581511
       :> 0x64f98fa7
       :> 0xbefa4fa4
       :> Nil

instance SHAInitials SHA256 where
  _H⁰ _ = 0x6a09e667
       :> 0xbb67ae85
       :> 0x3c6ef372
       :> 0xa54ff53a
       :> 0x510e527f
       :> 0x9b05688c
       :> 0x1f83d9ab
       :> 0x5be0cd19
       :> Nil

instance SHAInitials SHA384 where
  _H⁰ _ = 0xcbbb9d5dc1059ed8
       :> 0x629a292a367cd507
       :> 0x9159015a3070dd17
       :> 0x152fecd8f70e5939
       :> 0x67332667ffc00b31
       :> 0x8eb44a8768581511
       :> 0xdb0c2e0d64f98fa7
       :> 0x47b5481dbefa4fa4
       :> Nil

instance SHAInitials SHA512 where
  _H⁰ _ = 0x6a09e667f3bcc908
       :> 0xbb67ae8584caa73b
       :> 0x3c6ef372fe94f82b
       :> 0xa54ff53a5f1d36f1
       :> 0x510e527fade682d1
       :> 0x9b05688c2b3e6c1f
       :> 0x1f83d9abfb41bd6b
       :> 0x5be0cd19137e2179
       :> Nil

instance SHAInitials SHA512224 where
  _H⁰ _ = 0x8C3D37C819544DA2
       :> 0x73E1996689DCD4D6
       :> 0x1DFAB7AE32FF9C82
       :> 0x679DD514582F9FCF
       :> 0x0F6D2B697BD44DA8
       :> 0x77E36F7304C48942
       :> 0x3F9D85A86A1D36C8
       :> 0x1112E6AD91D692A1
       :> Nil

instance SHAInitials SHA512256 where
  _H⁰ _ = 0x22312194FC2BF72C
       :> 0x9F555FA3C84C64C2
       :> 0x2393B86B6F53B151
       :> 0x963877195940EABD
       :> 0x96283EE2A88EFFE3
       :> 0xBE5E1E2553863992
       :> 0x2B0199FC2C85B8AA
       :> 0x0EB72DDC81C52CA2
       :> Nil

---------------------------------------
-- Section 6: SECURE HASH ALGORITHMS --
---------------------------------------

-- | All of the algorithms defined in FIPS 180-4 share some similar
-- computation scheme, which is formalized using the 'SHAHashCompute'
-- class. It covers the following phases of the standard:
--
--  - Step "/1. Prepare the message schedule/": via '_W'
--  - Step "/3. For t=0 to .../": via 'computeCycle' (a single iteration only)
--
-- The remaining steps are formalized separately.
class SHAHashCompute alg where
  computeCycle ∷
    Proxy alg →
    ∀ t. t + 1 ≤ ScheduleCount alg ⇒
    SNat t → MessageBlock alg → HashValue alg → HashValue alg

instance SHAHashCompute SHA1 where
  computeCycle (alg ∷ Proxy alg) (t@SNat ∷ SNat t) m v =
    _T :> a :> _ROTL @30 SNat b :> c :> d :> Nil
   where
    _Wₜ = at @_ @(ScheduleCount alg - 1 - t) t _W
    _T = _ROTL @5 SNat a + _f t b c d + e + _K alg t + _Wₜ
    a = at @0 SNat v
    b = at @1 SNat v
    c = at @2 SNat v
    d = at @3 SNat v
    e = at @4 SNat v

    _W = smapWithBounds prepare $ repeat ()

    prepare ∷ ∀ n. n + 1 ≤ ScheduleCount SHA1 ⇒ SNat n → () → SHAWord SHA1
    prepare n@(SNat ∷ SNat n) _ =
      case compareSNat n (SNat @15) of
        SNatLE → at @n @(15 - n) SNat m
        SNatGT → _ROTL (SNat @1)
               $ at @(n -  3) @(ScheduleCount SHA1 - (n - 2))  SNat _W
               ⊕ at @(n -  8) @(ScheduleCount SHA1 - (n - 7))  SNat _W
               ⊕ at @(n - 14) @(ScheduleCount SHA1 - (n - 13)) SNat _W
               ⊕ at @(n - 16) @(ScheduleCount SHA1 - (n - 15)) SNat _W


instance SHAHashCompute SHA256 where
  computeCycle (alg ∷ Proxy alg) (t ∷ SNat t) m v =
    _T₁ + _T₂ :> a :> b :> c :> d + _T₁ :> e :> f :> g :> Nil
   where
    _Wₜ = at @_ @(ScheduleCount alg - 1 - t) t (_W# alg m)
    _T₁ = h + _Σ₁ alg e + _Ch e f g + _K alg t + _Wₜ
    _T₂ = _Σ₀ alg a + _Mai a b c
    a = at @0 SNat v
    b = at @1 SNat v
    c = at @2 SNat v
    d = at @3 SNat v
    e = at @4 SNat v
    f = at @5 SNat v
    g = at @6 SNat v
    h = at @7 SNat v

deriving via SHA256 instance SHAHashCompute SHA224

instance SHAHashCompute SHA512 where
  computeCycle (alg ∷ Proxy alg) (t ∷ SNat t) m v =
    _T₁ + _T₂ :> a :> b :> c :> d + _T₁ :> e :> f :> g :> Nil
   where
    _Wₜ = at @_ @(ScheduleCount alg - 1 - t) t (_W# alg m)
    _T₁ = h + _Σ₁ alg e + _Ch e f g + _K alg t + _Wₜ
    _T₂ = _Σ₀ alg a + _Mai a b c
    a = at @0 SNat v
    b = at @1 SNat v
    c = at @2 SNat v
    d = at @3 SNat v
    e = at @4 SNat v
    f = at @5 SNat v
    g = at @6 SNat v
    h = at @7 SNat v

deriving via SHA512 instance SHAHashCompute SHA384
deriving via SHA512 instance SHAHashCompute SHA512224
deriving via SHA512 instance SHAHashCompute SHA512256

-- | Message schedule preparation scheme of SHA256 and SHA512.
_W# ∷
  ∀ alg.
  (KnownNat (WordSize alg), KnownNat (ScheduleCount alg)) ⇒
  (SHAFunctions alg, 1 ≤ WordSize alg, 1 ≤ ScheduleCount alg) ⇒
  Proxy alg →
  MessageBlock alg →
  Vec (ScheduleCount alg) (SHAWord alg)
_W# alg m =
  let
    prepare ∷ ∀ t. t + 1 ≤ ScheduleCount alg ⇒ SNat t → () → SHAWord alg
    prepare t@(SNat ∷ SNat t) _ =
      case compareSNat t (SNat @15) of
        SNatLE → at @t @(15 - t) SNat m
        SNatGT
          | Dict ← leTrans @(t -  1) @(t + 1) @(ScheduleCount alg)
          , Dict ← leTrans @(t -  6) @(t + 1) @(ScheduleCount alg)
          , Dict ← leTrans @(t - 14) @(t + 1) @(ScheduleCount alg)
          , Dict ← leTrans @(t - 15) @(t + 1) @(ScheduleCount alg)
          → _σ₁ alg (at @(t -  2) @(ScheduleCount alg - (t - 1))  SNat wV)
          +          at @(t -  7) @(ScheduleCount alg - (t - 6))  SNat wV
          + _σ₀ alg (at @(t - 15) @(ScheduleCount alg - (t - 14)) SNat wV)
          +          at @(t - 16) @(ScheduleCount alg - (t - 15)) SNat wV
    {-# NOINLINE prepare #-}

    wV ∷ Vec (ScheduleCount alg) (SHAWord alg)
    wV = smapWithBounds prepare $ repeat ()
    {-# NOINLINE wV #-}
  in
    wV