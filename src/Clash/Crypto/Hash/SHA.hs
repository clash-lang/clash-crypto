{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Clash.Crypto.Hash.SHA where

import Clash.Prelude
import Clash.Sized.Internal.BitVector

import qualified Clash.Signal.Delayed.Bundle as DSignal

import Data.Constraint
import Data.Either
import Control.Arrow
import Data.Proxy
import Data.Type.Bool
import Data.Type.Equality
import GHC.TypeLits.KnownNat
import Unsafe.Coerce (unsafeCoerce)

import qualified GHC.TypeNats as GHC (natVal)

infix 4 ≤
type (≤) ∷ ∀ {n}. n → n → Constraint
type (≤) x y = (<=) x y

type SHA ∷ Type
data SHA =
    SHA1
  | SHA224
  | SHA256
  | SHA384
  | SHA512
  | SHA512224
  | SHA512256

type WordSize ∷ SHA → Nat
type family WordSize alg where
  WordSize SHA1   = 32
  WordSize SHA224 = 32
  WordSize SHA256 = 32
  WordSize _      = 64

type BlockSize ∷ SHA → Nat
type family BlockSize alg where
  BlockSize SHA1   = 512
  BlockSize SHA224 = 512
  BlockSize SHA256 = 512
  BlockSize _      = 1024

type MessageBlockWords ∷ SHA → Nat
type family MessageBlockWords alg where
  MessageBlockWords SHA1 = 5
  MessageBlockWords _    = 8

type MessageDigestSize ∷ SHA → Nat
type family MessageDigestSize alg where
  MessageDigestSize SHA1      = 160
  MessageDigestSize SHA224    = 224
  MessageDigestSize SHA256    = 256
  MessageDigestSize SHA384    = 384
  MessageDigestSize SHA512    = 512
  MessageDigestSize SHA512224 = 224
  MessageDigestSize SHA512256 = 256

type ScheduleCount ∷ SHA → Nat
type family ScheduleCount alg where
  ScheduleCount SHA224 = 64
  ScheduleCount SHA256 = 64
  ScheduleCount _      = 80

type HashBlock (alg ∷ SHA) =
  Vec (MessageBlockWords alg) (BitVector (WordSize alg))

type Message (ℓ ∷ Nat) = BitVector ℓ

type MessageBlock (alg ∷ SHA) =
  Vec 16 (BitVector (WordSize alg))

type WordType (alg ∷ SHA) = BitVector (WordSize alg)

data SHAFacts (alg ∷ SHA) where
  SHAFacts ∷
    ( KnownNat (WordSize alg)
    , KnownNat (BlockSize alg)
    , KnownNat (MessageBlockWords alg)
    , KnownNat (MessageDigestSize alg)
    , KnownNat (ScheduleCount alg)
    , SHAInitials alg
    , SHAHashCompute alg
    , 1 ≤ BlockSize alg
    , 1 ≤ ScheduleCount alg
    , 1 ≤ WordSize alg
    , 2 ^ SizeBits alg
        ~ BlockSize alg * Div (2 ^ SizeBits alg) (BlockSize alg)
    , 2 * BlockSize alg ≤ Div (2 ^ SizeBits alg) (BlockSize alg)
    , MessageDigestSize alg ≤ MessageBlockWords alg * WordSize alg
    , BlockSize alg ~ 16 * WordSize alg
    , Mod (MessageDigestSize alg) 8 ~ 0
    ) ⇒
    Proxy alg →
    SHAFacts alg

class    KnownSHA alg       where knownSHA ∷ SHAFacts alg
instance KnownSHA SHA1      where knownSHA = SHAFacts Proxy
instance KnownSHA SHA224    where knownSHA = SHAFacts Proxy
instance KnownSHA SHA256    where knownSHA = SHAFacts Proxy
instance KnownSHA SHA384    where knownSHA = SHAFacts Proxy
instance KnownSHA SHA512    where knownSHA = SHAFacts Proxy
instance KnownSHA SHA512224 where knownSHA = SHAFacts Proxy
instance KnownSHA SHA512256 where knownSHA = SHAFacts Proxy

-- 2.2.2 Symbols and Operations

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

-- prove:
--   ROTL (SNat @n) x ≡ ROTR (SNat @(w - n)) x
--   ROTR (SNat @n) x ≡ ROTL (SNat @(w - n)) x

_SHR ∷ ∀ n w. (KnownNat w, n ≤ w) ⇒ SNat n → BitVector w → BitVector w
_SHR n x = x ≫ n

-- 4.1 Functions

_Ch ∷ KnownNat w ⇒ BitVector w → BitVector w → BitVector w → BitVector w
_Ch x y z = (x ∧ y) ⊕ ((¬) x ∧ z)

_Mai ∷ KnownNat w ⇒ BitVector w → BitVector w → BitVector w → BitVector w
_Mai x y z = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)

_Parity ∷ KnownNat w ⇒ BitVector w → BitVector w → BitVector w → BitVector w
_Parity x y z = x ⊕ y ⊕ z

_f ∷ t ≤ 79 ⇒ SNat t → BitVector 32 → BitVector 32 → BitVector 32 → BitVector 32
_f t
  | SNatLE ← compareSNat t (SNat @19) = _Ch
  | SNatLE ← compareSNat t (SNat @39) = _Parity
  | SNatLE ← compareSNat t (SNat @59) = _Mai
  | otherwise                         = _Parity

class SHAFunctions (alg ∷ SHA) where
  _Σ₀ ∷ Proxy alg → WordType alg → WordType alg
  _Σ₁ ∷ Proxy alg → WordType alg → WordType alg
  _σ₀ ∷ Proxy alg → WordType alg → WordType alg
  _σ₁ ∷ Proxy alg → WordType alg → WordType alg

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

class SHAConstants (alg ∷ SHA) where
  type MaxIndex alg ∷ Nat
  _K ∷ Proxy alg → ∀ t. t ≤ MaxIndex alg ⇒ SNat t -> WordType alg

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
    v ∷ Vec (MaxIndex SHA224 + 1) (WordType SHA224)
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
    v ∷ Vec (MaxIndex SHA384 + 1) (WordType SHA384)
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

class SHAInitials (alg ∷ SHA) where
  _H⁰ ∷ Proxy alg → HashBlock alg

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

class SHAHashCompute alg where
  _W ∷
    Proxy alg →
    ∀ t. t + 1 ≤ ScheduleCount alg ⇒
    SNat t → MessageBlock alg → WordType alg

  computeCycle ∷
    Proxy alg →
    ∀ t. t + 1 ≤ ScheduleCount alg ⇒
    SNat t → MessageBlock alg → HashBlock alg → HashBlock alg

instance SHAHashCompute SHA1 where
  _W alg t@(SNat ∷ SNat t) m = case compareSNat t (SNat @15) of
    SNatLE → at @t @(15 - t) SNat m
    SNatGT → _ROTL (SNat @1)
           $ _W alg (SNat @(t -  3)) m
           ⊕ _W alg (SNat @(t -  8)) m
           ⊕ _W alg (SNat @(t - 14)) m
           ⊕ _W alg (SNat @(t - 16)) m

  computeCycle alg t m v =
    _T :> a :> _ROTL @30 SNat b :> c :> d :> Nil
   where
    _T = _ROTL @5 SNat a + _f t b c d + e + _K alg t + _W alg t m
    a = at @0 SNat v
    b = at @1 SNat v
    c = at @2 SNat v
    d = at @3 SNat v
    e = at @4 SNat v

instance SHAHashCompute SHA256 where
  _W alg t@(SNat ∷ SNat t) m = case compareSNat t (SNat @15) of
    SNatLE → at @t @(15 - t) SNat m
    SNatGT → _σ₁ alg (_W alg (SNat @(t -  2)) m)
           +          _W alg (SNat @(t -  7)) m
           + _σ₀ alg (_W alg (SNat @(t - 15)) m)
           +          _W alg (SNat @(t - 16)) m

  computeCycle alg t m v =
    _T₁ + _T₂ :> a :> b :> c :> d + _T₁ :> e :> f :> g :> Nil
   where
    _T₁ = h + _Σ₁ alg e + _Ch e f g + _K alg t + _W alg t m
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
  _W alg t@(SNat ∷ SNat t) m = case compareSNat t (SNat @15) of
    SNatLE → at @t @(15 - t) SNat m
    SNatGT → _σ₁ alg (_W alg (SNat @(t -  2)) m)
           +          _W alg (SNat @(t -  7)) m
           + _σ₀ alg (_W alg (SNat @(t - 15)) m)
           +          _W alg (SNat @(t - 16)) m

  computeCycle alg t m v =
    _T₁ + _T₂ :> a :> b :> c :> d + _T₁ :> e :> f :> g :> Nil
   where
    _T₁ = h + _Σ₁ alg e + _Ch e f g + _K alg t + _W alg t m
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

computeBlock ∷
  ∀ (alg ∷ SHA). KnownSHA alg ⇒
  ∀ stages. stages ≤ ScheduleCount alg ⇒
  SNat stages →
  ∀ dom n. (KnownDomain dom, HiddenClockResetEnable dom) ⇒
  DSignal dom n (HashBlock alg) →
  DSignal dom n (MessageBlock alg) →
  DSignal dom (n + stages) (HashBlock alg)
computeBlock stages@SNat hbs mbs
  | SHAFacts{} ← knownSHA @alg
    -- using 'forward' is safe here, as 'dsFold' keeps the input
    -- stable for exactly @stages@ many cycles
  = ((zipWith (+) <$> forward stages hbs) <*>)
  $ fmap snd
  $ distributeStages stages undefined (computeCycles @alg)
  $ DSignal.bundle (mbs, hbs)

computeCycles ∷
  ∀ (alg ∷ SHA). KnownSHA alg ⇒
  Vec (ScheduleCount alg)
    ( (MessageBlock alg, HashBlock alg)
    → (MessageBlock alg, HashBlock alg)
    )
computeCycles
  | SHAFacts alg ← knownSHA @alg
  = smapWithBounds @(ScheduleCount alg) computeCycle'
  $ repeat @(ScheduleCount alg - 1 + 1) alg
 where
  -- TODO: don't copy m, forward the signal instead
  computeCycle' t alg (m, v) =
    (m, computeCycle alg t m v)

-- | Evenly distributes @d@ registers between @n@ combinational
-- computations. The registers are all initialized with the provided
-- initial value. The introduced delay is tracked using 'DSignal'.
distributeStages ∷
  ∀ (d ∷ Nat) (n ∷ Nat) (a ∷ Type).
  (KnownNat n, NFDataX a) ⇒
  SNat d →
  a →
  Vec n (a → a) →
  ∀ (dom ∷ Domain) (k ∷ Nat).
  (KnownDomain dom, HiddenClockResetEnable dom) ⇒
  DSignal dom k a →
  DSignal dom (k + d) a
distributeStages d@SNat x vec =
  distributeStages# (SNat @0) d $ reverse vec
 where
  distributeStages# ∷
    ∀ (m ∷ Nat) (i ∷ Nat) (r ∷ Nat).
    (KnownNat m, NFDataX a) ⇒
    SNat i → SNat r →
    Vec m (a → a) →
    ∀ (dom ∷ Domain) (k ∷ Nat).
    (KnownDomain dom, HiddenClockResetEnable dom) ⇒
    DSignal dom k a →
    DSignal dom (k + r) a
  distributeStages# i@SNat r@SNat cs = case toUNat @m SNat of
    UZero   → delayedI x
    USucc _ → case toUNat r of
      UZero
        → fmap (head cs)
        . distributeStages# (succSNat i) r (tail cs)
      USucc _
        | Dict ← atMostOnePerStage @n @d @i
        , Dict ← leTrans @(DistributedStages n d i) @1 @(r - 1 + 1)
        → delayedI @(DistributedStages n d i) x
        . fmap (head cs)
        . distributeStages#
            (succSNat i)
            (SNat @(r - DistributedStages n d i))
            (tail cs)

-- | A type family for calculating the positions at which we need to
-- put a register in front, if we like to evenly distribute m
-- registers between a chain of n circuit blocks, where m < n.
type DistributedStages ∷ Nat → Nat → Nat → Nat
type family DistributedStages n d i where
  DistributedStages _ 0 _ = 0
  DistributedStages n d i =
    If (n <=? d)
      1
      ( If (  1 <=? i
              -- ^ we don't place a register before the first element
           && If (i <=? Mod n (d + 1) * (Div n (d + 1) + 1))
                 -- ^ distribute the hangover blocks to the first r chains
                (Mod i (Div n (d + 1) + 1) == 0)
                (Mod
                   (i - Mod n (d + 1) * (Div n (d + 1) + 1))
                   (Div n (d + 1)) == 0)
           )
          1 0
      )

{- some quick test code for the 'DistributedStages' type family

placeRegister ∷ Nat → Nat → IO ()
placeRegister n m = do
  print (k, r, b)
  putStrLn "---"
  forM_ chain $ \(i, c) → do
    when c $ putStrLn "[R]"
    putStr " "
    print i
 where
  -- minimum size of chained blocks without a register in between
  k = n `div` (m + 1)
  -- number of hangover blocks
  r = n `mod` (m + 1)
  -- add-one-more range bound
  b = (k + 1) * r

  chain
    | m <= 0    = ( , False) <$> [0..n-1]
    | m >= n    = (0, False) : (( , True) <$> [1..n-1])
    | otherwise =
        [ (i, i > 0 && cond)
        | i <- [0..n-1]
        , let cond = if i <= b
                     then i `mod` (k + 1) == 0
                     else (i - b) `mod` k == 0
        ]
-- -}

instance
  (KnownNat n, KnownNat m, KnownNat i) ⇒
  KnownNat3 $(nameToSymbol ''DistributedStages) n m i
 where
  natSing3 =
    let
      n = GHC.natVal (Proxy @n)
      m = GHC.natVal (Proxy @m)
      i = GHC.natVal (Proxy @i)
      r = f n m i
    in
      SNatKn r
   where
    f ∷ Nat → Nat → Nat → Nat
    f n m i
      | n == 0 = 0
      | n <= m = 1
      | otherwise =
          let k = n `div` (m + 1)
              r = n `mod` (m + 1)
              b = (k + 1) * r
           in if 1 <= i &&
                   if i <= b
                   then mod i (k + 1) == 0
                   else mod (i - b) k == 0
              then 1
              else 0
  {-# INLINE natSing3 #-}

-- | We never distribute more than one register per stage. The
-- property trivially holds, as the first conditional only selects
-- between the constants zero and one.
atMostOnePerStage ∷ ∀x y z. Dict (DistributedStages x y z ≤ 1)
atMostOnePerStage = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

-- | Divisible division operation, which ensures that the dividend is
-- always a multiple of the divisor. Type family resolution will get
-- /stuck/ if the dividend is not a multiple of the divisor.
type family DDiv (a :: Nat) (b :: Nat) :: Nat where
  DDiv a b = DDivCheck (Mod a b) a b

-- | Helper type family for checking the reminder of
-- 'DDiv'. Unfortunately type families cannot be scoped.
type family DDivCheck (a :: Nat) (b :: Nat) (c :: Nat) :: Nat where
  DDivCheck 0 a b = Div a b

-- | If the dividend is a multiple of the of the divisor, then 'DDiv'
-- and 'Div' return the same result.
condDivEqDDivFact ∷
  ∀ (a ∷ Nat) (b ∷ Nat).
  (1 ≤ b, Mod a b ~ 0) ⇒
  Dict (DDiv a b ~ Div a b)
condDivEqDDivFact = unsafeCoerce (Dict ∷ Dict (0 ~ 0))

hashStream ∷
  ∀ (alg ∷ SHA) (dom ∷ Domain) (n ∷ Nat) (k ∷ Nat).
  (KnownNat k, KnownSHA alg, KnownDomain dom, HiddenClockResetEnable dom) ⇒
  (KnownNat n, 1 ≤ n, n ≤ BlockSize alg, Mod (BlockSize alg) n ~ 0) ⇒
  Div (BlockSize alg) n ≤ ScheduleCount alg ⇒
  DSignal dom k (Maybe (Either () (BitVector n))) →
  ( DSignal dom (k + DDiv (BlockSize alg) n) (Maybe (HashBlock alg))
  , ( DSignal dom k (Vec (DDiv (BlockSize alg) n - 1) (BitVector n))
    , DSignal dom k (Index (DDiv (BlockSize alg) n))
    , DSignal dom k Bool
    , DSignal dom (k + 1) (MessageBlock alg)
    , DSignal dom (k + DDiv (BlockSize alg) n) Bool
    , DSignal dom (k + DDiv (BlockSize alg) n) Bool
    , DSignal dom (k + DDiv (BlockSize alg) n) (HashBlock alg)
    )
  )
hashStream input
  | SHAFacts alg ← knownSHA @alg
  , Dict ← condDivEqDDivFact @(BlockSize alg) @n
  , Dict ← lemma₀ @(BlockSize alg) @n
  , Dict ← lemma₁ @(16 * WordSize alg) @n
  , Dict ← lemma₂ @(Div (BlockSize alg) n) @(ScheduleCount alg)
  =
  let
    -- some buffer to shift in @(BlockSize alg / n) - 1@ frames
    -- for glueing them together into a @BlockSize alg - n@ sized block
    collector ∷ DSignal dom k (Vec (DDiv (BlockSize alg) n - 1) (BitVector n))
    collector = antiDelay d1 $ delayedI @1 (repeat 0)
      $ (\x → maybe x (either (const x) (fst . shiftInAtN x . (:> Nil))))
          <$> collector
          <*> input

    -- counter that counts down on receiving some input until enough frames
    -- have been collected creating a block
    releaseCount ∷ DSignal dom k (Index (DDiv (BlockSize alg) n))
    releaseCount = antiDelay d1 $ delayedI @1 maxBound
      $ (\x → maybe x (fromRight maxBound . (satPred SatWrap x <$)))
          <$> releaseCount
          <*> input

    -- keep the data from the collector stable until the releaseCount
    -- reaches zero
    keepStable ∷ DSignal dom k Bool
    keepStable = (> 0) <$> releaseCount

    -- full message block copied over from the collector after the
    -- arrival of the @BlockSize alg / n@-th frame
    msgBlock ∷ DSignal dom (k + 1) (MessageBlock alg)
    msgBlock = delayedI @1 (repeat 0)
      $ mux keepStable (antiDelay d1 msgBlock)
      $ fmap bitCoerce
      $ (++) <$> collector
             <*> ((:> Nil) . maybe 0 (fromRight 0) <$> input)

{-
    -- proceed with the next fold immediately after all computation is
    -- done, where we require at least a one cycle delay.
    proceedCount ∷
      DSignal dom k (Maybe (Index (k + DDiv (BlockSize alg) n)))
    proceedCount = antiDelay d1 $ delayedI @1 Nothing
      $ mux ((== 0) <$> releaseCount)
          (pure $ Just maxBound)
          (maybe Nothing (\x → if x > 0 then Just $ x - 1 else Nothing)
             <$> proceedCount
          )

    proceed ∷ DSignal dom (k + DDiv (BlockSize alg) n) Bool
    proceed = (== (Just 0)) <$> forward SNat proceedCount
-}

    -- TODO: optimize @delayedI@; use a counter instead, see commented
    -- code above
    proceed ∷ DSignal dom (k + DDiv (BlockSize alg) n) Bool
    proceed = delayedI False $ (== 0) <$> releaseCount

    -- TODO: align with proceed; the end of the message alwasy is one
    -- cycle behind the last 'proceed' trigger
    endOfMessage ∷ DSignal dom (k + DDiv (BlockSize alg) n) Bool
    endOfMessage = delayedI False $ (== (Just $ Left ())) <$> input

    rstF ∷ Reset dom
    rstF = unsafeFromActiveHigh $ toSignal $ delayedI @1 False endOfMessage

    hashBlock ∷ DSignal dom (k + DDiv (BlockSize alg) n) (HashBlock alg)
    hashBlock = withReset rstF $
      dsFold
        (_H⁰ alg)
        proceed
        (computeBlock @alg @(DDiv (BlockSize alg) n - 1) SNat)
        msgBlock
  in
    ( mux endOfMessage
        (Just <$> hashBlock)
        (pure Nothing)
    , ( collector
      , releaseCount
      , keepStable
      , msgBlock
      , proceed
      , endOfMessage
      , hashBlock
      )
    )

 where
  lemma₀ ∷
    ∀ (a ∷ Nat) (b ∷ Nat).
    (1 ≤ a, 1 ≤ b, Mod a b ~ 0) ⇒
    Dict (1 ≤ Div a b)
  lemma₀ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  lemma₁ ∷
    ∀ (a ∷ Nat) (b ∷ Nat).
    (1 ≤ Div a b, Mod a b ~ 0) ⇒
    Dict (((Div a b - 1) + 1) * b ~ a)
  lemma₁ = unsafeCoerce (Dict ∷ Dict (0 ~ 0))

  lemma₂ ∷
    ∀ (a ∷ Nat) (b ∷ Nat).
    (1 ≤ a, a ≤ b) ⇒
    Dict (a - 1 ≤ b)
  lemma₂ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

-- | Temporally folds a signal over time. The folding function is
-- allowed to introduce an m-cycle delay and is assumed to require the
-- inputs to be stable for at least @m@ cycles. 'dsFold' takes care
-- about satisifying the stability requirements for the accumulator,
-- but stability of the input stream needs the asserted outside of
-- 'dsFold', simiply for the reason of minimizing register usage, as
-- the latches for keeping the input streams stable also may be used
-- elsewhere.
--
-- A step trigger is used to start the next round of a fold, where
-- every two consequitve assertions the trigger must be at least @m@
-- cycles apart.
--
-- TODO: model the aformentioned assumptions as part of the type.
dsFold ∷
  forall dom b a k m.
  (HiddenClockResetEnable dom, NFDataX b, KnownNat m, 1 ≤ k + m) ⇒
  b →
  -- ^ initial value of the accumulator (only set after releasing the
  -- reset)
  DSignal dom (k + m) Bool →
  -- ^ step trigger
  (DSignal dom k b → DSignal dom k a → DSignal dom (k + m) b) →
  -- ^ function / circuit to be folded
  DSignal dom k a →
  -- ^ input stream
  DSignal dom (k + m) b
  -- ^ output stream
dsFold ival trg circuit is = result
 where
  result = gate (circuit (antiDelay (SNat @m) acc) is) acc

  acc ∷ DSignal dom (k + m) b
  acc = delayedI @1 @b @dom @(k + m - 1) ival $ antiDelay d1 result

  gate ∷ DSignal dom (k + m) b → DSignal dom (k + m) b → DSignal dom (k + m) b
  gate = case compareSNat @m @0 SNat SNat of
    -- Check: https://github.com/clash-lang/clash-compiler/pull/2784
    SNatLE → const
    SNatGT → mux trg

hash ∷
  ∀ (alg ∷ SHA) (dom ∷ Domain).
  (KnownSHA alg, KnownDomain dom, HiddenClockResetEnable dom) ⇒
  Signal dom (Maybe (MessageBlock alg)) →
  Signal dom (Maybe (BitVector (MessageDigestSize alg)))
hash mb | SHAFacts alg ← knownSHA @alg =
  let
    NotStarted ~~> (Nothing, _) = (NotStarted,        Right Nothing    )
    ResultIs x ~~> (Nothing, _) = (ResultIs x,        Right x          )
    Running x  ~~> (Nothing, _) = (ResultIs $ Just x, Right $ Just x   )
    Running x  ~~> (Just b,  c) = (Running c,         Left (b, x)      )
    _          ~~> (Just b,  c) = (Running c,         Left (b, _H⁰ alg))

    r ∷ Signal dom ( Either (MessageBlock alg, HashBlock alg)
                            (Maybe (HashBlock alg))
                   )
    r = mealy (~~>) NotStarted $ bundle (mb, toSignal computed)

    -- this function only works without registers right now
    computed ∷ DSignal dom 0 (HashBlock alg)
    computed = computeBlock @alg (SNat @0)
      (snd . fromLeft undefined <$> fromSignal r)
      (fst . fromLeft undefined <$> fromSignal r)
  in
    either (const Nothing) (fmap (resize . pack)) <$> r

pattern NotStarted ∷ (Maybe a, Bool)
pattern NotStarted = (Nothing, False)

pattern Running ∷ a → (Maybe a, Bool)
pattern Running x = (Just x, False)

pattern ResultIs ∷ Maybe a → (Maybe a, Bool)
pattern ResultIs x = (x, True)

{-# COMPLETE NotStarted, Running, ResultIs #-}

-- Preprocessing

type SizeBits alg = 2 * WordSize alg

type family PaddingZeros (alg ∷ SHA) (ℓ ∷ Nat) ∷ Nat where
  PaddingZeros alg ℓ =
    RequiredBlocks alg ℓ * BlockSize alg
      - Mod ℓ (BlockSize alg)
      - 1
      - SizeBits alg

type family RequiredBlocks (alg ∷ SHA) (ℓ ∷ Nat) ∷ Nat where
  RequiredBlocks alg ℓ =
    If (1 + SizeBits alg <=? BlockSize alg - Mod ℓ (BlockSize alg)) 1 2

padMessage ∷
  ∀ (alg ∷ SHA) (ℓ ∷ Nat).
  (KnownSHA alg, KnownNat ℓ) ⇒
  Message ℓ →
  Message (ℓ + 1 + PaddingZeros alg ℓ + SizeBits alg)
padMessage m
  | SHAFacts{} ← knownSHA @alg
  , Dict ← modBound @ℓ @(BlockSize alg)
  , Dict ← p₀
  , Dict ← p₁
  , Dict ← p₂
  =
  m ++# (1 ∷ BitVector 1)
    ++# (0 ∷ BitVector (PaddingZeros alg ℓ))
    ++# pack (natToNum @ℓ @(Unsigned (SizeBits alg)))
 where
  -- required proofs
  p₀ ∷ Dict (1 ≤ RequiredBlocks alg ℓ * BlockSize alg - Mod ℓ (BlockSize alg))
  p₀ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  p₁ ∷ Dict (Mod ℓ (BlockSize alg) ≤ RequiredBlocks alg ℓ * BlockSize alg)
  p₁ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  p₂ ∷ Dict
    ( SizeBits alg ≤
        RequiredBlocks alg ℓ * BlockSize alg
          - Mod ℓ (BlockSize alg)
          - 1
    )
  p₂ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

-- | The number of n-bit frames required to store the size of the
-- message.
type ReqSizeFrames alg n =
  If (n <=? SizeBits alg)
    (Div (SizeBits alg) n + If (Mod n (SizeBits alg) <=? 0) 0 1)
    1

reqSizeFramesGeOneGeneralizedFact ∷
  ∀ (a ∷ Nat) (b ∷ Nat).
  1 ≤ b ⇒
  Dict (1 ≤ If (b <=? a) (Div a b + If (Mod b a <=? 0) 0 1) 1)
reqSizeFramesGeOneGeneralizedFact = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

-- | We store the message size in terms of the number of n-bit frames
-- + some remaining bits required to hold the whole message.
data MsgBits (alg ∷ SHA) (n ∷ Nat) =
  MsgBits
    { frameCount ∷ Index (DDiv (2 ^ SizeBits alg) n)
      -- ^ number of full n-bit frames required to store the message
    , remainder ∷ Index n
      -- ^ number of remaining bits to complete the message
    }
  deriving (Generic, NFDataX)

deriving instance
  ( KnownNat n, 1 ≤ n, KnownNat (DDiv (2 ^ SizeBits alg) n)
  , 1 <= DDiv (2 ^ SizeBits alg) n
  ) ⇒
  BitPack (MsgBits alg n)

-- | All information necessary for filling the message padding in a
-- n-bit frame cycles. The message pad can be computed as soon as
-- the size of the message is known.
data MsgPad (alg ∷ SHA) (n ∷ Nat) =
  MsgPad
    { remainingFrames ∷ Index (2 * BlockSize alg)
      -- ^ the remaining frames still to be output for completing
      -- the padded message
    , remainingSizeFrames ∷ Index (2 * BlockSize alg)
      -- ^ the remaining number of frames containing the size of
      -- the message
    , msgSize ∷ Vec (ReqSizeFrames alg n) (BitVector n)
      -- ^ the frames containing the actual size of the message
    , terminated ∷ Bool
      -- ^ indicates whether the message has already been terminated
    }
  deriving (Generic)

deriving instance
  ( KnownNat n, KnownNat (WordSize alg)
  , 1 ≤ n, 1 ≤ SizeBits alg
  ) ⇒
  NFDataX (MsgPad alg n)

deriving instance
  ( KnownNat n, KnownNat (WordSize alg), KnownNat (BlockSize alg)
  , 1 ≤ n, 1 ≤ SizeBits alg, 1 ≤ 2 * BlockSize alg
  ) ⇒
  BitPack (MsgPad alg n)

-- | Extends the input message via adding some padding to ensure that
-- the message's length is always a multiple of 'BlockSize alg'.
padMessageStream ∷
  ∀ (alg ∷ SHA) (dom ∷ Domain) (n ∷ Nat).
  (KnownSHA alg, KnownDomain dom, HiddenClockResetEnable dom, KnownNat n) ⇒
  (1 ≤ n, n ≤ BlockSize alg, Mod (BlockSize alg) n ~ 0) ⇒
  Signal dom (Maybe (BitVector n, Maybe (Index (n + 1)))) →
  -- ^ Input stream for passing messages (see 'sha' fore mode details
  -- on the data serialization).
  Signal dom (Maybe (Either () (BitVector n)))
  -- ^ Output message stream, where messages are padded according to
  -- the SHA standard. As for the input, the actual data may be
  -- non-continuous. The message is terminated by @Left ()@, while all
  -- data frames are @Right@-wrapped instead. Note that, in contrast
  -- to the input, the bitsize of the message will always be aligned
  -- with the frame size @n@.
padMessageStream
  | SHAFacts{} ← knownSHA @alg
  , Dict ← fact₁
  = mealy (~~>) $ Left $ MsgBits 0 0
 where
  (~~>) ∷
    (KnownNat (DDiv (2 ^ SizeBits alg) n), KnownNat (BlockSize alg)) ⇒
    Either (MsgBits alg n) (MsgPad alg n) →
    Maybe (BitVector n, Maybe (Index (n + 1))) →
    ( Either (MsgBits alg n) (MsgPad alg n)
    , Maybe (Either () (BitVector n))
    )

  -- no input
  state@(Left _) ~~> Nothing
    = (state, Nothing)

  -- non-terminal data input
  Left (MsgBits s r) ~~> Just (d, Nothing)
    = ( Left $ MsgBits (s + 1) r
      , Just $ Right d
      )

  -- end of input / start padding
  Left msgBits ~~> Just (d, Just e)
    = initiatePaddingWith msgBits d e

  -- add padding
  Right msgPad ~~> _
    = addPaddingWith msgPad

  -------------------------------------------

  initiatePaddingWith ∷
    KnownNat (DDiv (2 ^ SizeBits alg) n) ⇒
    MsgBits alg n →
    BitVector n →
    Index (n + 1) →
    ( Either (MsgBits alg n) (MsgPad alg n)
    , Maybe (Either () (BitVector n))
    )
  initiatePaddingWith (MsgBits s _) dLast trim
    = terminate dLast trim
    $ addPaddingWith
    $ createMsgPad
    $ if natToNum @n == trim
      then MsgBits s 0
      else MsgBits (s + 1)
        $ truncateB @_ @n @1
        $ natToNum @n - trim

  terminate ∷
    BitVector n →
    Index (n + 1) →
    ( Either (MsgBits alg n) (MsgPad alg n)
    , Maybe (Either () (BitVector n))
    ) →
    ( Either (MsgBits alg n) (MsgPad alg n)
    , Maybe (Either () (BitVector n))
    )
  terminate dLast trim (ePad, meVec)
    | trim == natToNum @n
    = ( ePad
      , fmap ( ((1 ∷ BitVector 1) ++#)
             . truncateB# @(n-1) @1
             ) <$> meVec
      )

    | trim == 0
    = ( (\p → p { terminated = False }) <$> ePad
      , Just $ Right dLast
      )

    | SHAFacts{} ← knownSHA @alg
    , Dict ← fact₀
    = let c = fromEnum trim
       in ( ePad
          , fmap ( or# (shiftL# (shiftR# dLast c) c)
                 . \b → replaceBit# b (c - 1) high
                 ) <$> meVec
          )

  addPaddingWith ∷
    MsgPad alg n →
    ( Either (MsgBits alg n) (MsgPad alg n)
    , Maybe (Either () (BitVector n))
    )
  addPaddingWith p@MsgPad{..}
    | remainingFrames > remainingSizeFrames
    , SHAFacts{} ← knownSHA @alg
    = ( Right p
          { remainingFrames = remainingFrames - 1
          }
      , Just $ Right $
          if terminated
          then 0
          else (1 ∷ BitVector 1) ++# (0 :: BitVector (n - 1))
      )

    | otherwise
    , SHAFacts{} ← knownSHA @alg
    , Dict ← fact₁
    , Dict ← reqSizeFramesGeOneGeneralizedFact @(SizeBits alg) @n
    = ( if remainingSizeFrames > 0
        then Right p { remainingFrames = remainingFrames - 1
                     , remainingSizeFrames = remainingSizeFrames - 1
                     , msgSize = fst $ shiftInAtN msgSize (0 :> Nil)
                     }
        else Left (MsgBits 0 0)
      , if remainingSizeFrames == 0
        then Just $ Left ()
        else Just $ Right $
               let d = head @(ReqSizeFrames alg n - 1) msgSize
                in if terminated
                   then d
                   else (1 ∷ BitVector 1) ++# truncateB# @(n-1) @1 d
      )

  createMsgPad ∷ MsgBits alg n → MsgPad alg n
  createMsgPad (MsgBits s r)
    | SHAFacts{} ← knownSHA @alg
    = MsgPad
        { remainingFrames =
            let
              nFits ∷ Num a ⇒ a
              nFits = natToNum @(DDiv (BlockSize alg) n)
              -- ^ number of n-bit frames fitting into a message block
              truncateB₀ =
                truncateB @Index
                  @(2 * BlockSize alg)
                  @(DDiv (2 ^ SizeBits alg) n - 2 * BlockSize alg)
              -- ^ specialized 'truncateB'
              rFrames ∷ Index (2 * BlockSize alg)
              rFrames
                | Dict ← fact₀
                , Dict ← fact₁
                = nFits - truncateB₀ (mod s nFits)
              -- ^ number of n-bit frames that still must be padded
              -- within the current message block
              overhead
                | 1 + natToNum @(SizeBits alg) <= rFrames * natToNum @n = 0
                | otherwise = nFits
              -- ^ extend by one message block if the required padding
              -- information won't fit otherwise
            in
              rFrames + overhead

        , remainingSizeFrames =
            natToNum @(ReqSizeFrames alg n)

        , msgSize = bitCoerce $
            let
              u ∷ Unsigned (n * ReqSizeFrames alg n)
              u = unpack (extend₀ (pack₀ s)) * natToNum @n
                + unpack (extend₁ (pack r))
            in
              u
        , terminated = True
        }

  pack₀ ∷
    Index (DDiv (2 ^ SizeBits alg) n) →
    BitVector (CLog 2 (Div (2 ^ SizeBits alg) n))
  pack₀
    | SHAFacts{} ← knownSHA @alg
    , Dict ← fact₀
    , Dict ← fact₁
    , Dict ← leTrans @1 @(2 * BlockSize alg) @(Div (2 ^ SizeBits alg) n)
    = pack

  extend₀ ∷
    BitVector (CLog 2 (Div (2 ^ SizeBits alg) n)) →
    BitVector (n * ReqSizeFrames alg n)
  extend₀
    | SHAFacts{} ← knownSHA @alg
    , Dict ← fact₀
    , Dict ← leTrans @1 @(2 * BlockSize alg) @(Div (2 ^ SizeBits alg) n)
    , Dict ← lemma₀ @(SizeBits alg) @n
    = extend @BitVector
        @(CLog 2 (Div (2 ^ SizeBits alg) n))
        @(n * ReqSizeFrames alg n - CLog 2 (Div (2 ^ SizeBits alg) n))
   where
    lemma₀ ∷
      ∀ (a ∷ Nat) (b ∷ Nat).
      1 ≤ b ⇒
      Dict ( CLog 2 (Div (2 ^ a) b)
           ≤ b * (If (b <=? a) (Div a b + If (Mod b a <=? 0) 0 1) 1)
           )
    lemma₀ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  extend₁ ∷
    BitVector (CLog 2 n) →
    BitVector (n * ReqSizeFrames alg n)
  extend₁
    | SHAFacts{} ← knownSHA @alg
    , Dict ← reqSizeFramesGeOneGeneralizedFact @(SizeBits alg) @n
    , Dict ← lemma₀ @n @(ReqSizeFrames alg n)
    = extend @BitVector
        @(CLog 2 n)
        @(n * ReqSizeFrames alg n - CLog 2 n)
   where
    lemma₀ ∷
      ∀ (a ∷ Nat) (b ∷ Nat).
      1 ≤ b ⇒
      Dict (CLog 2 a ≤ a * b)
    lemma₀ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  fact₀ ∷ Dict (2 * BlockSize alg <= Div (2 ^ SizeBits alg) n)
  fact₀
    | SHAFacts{} ← knownSHA @alg
    , Dict ← modBound @(BlockSize alg) @n
    , Dict ← lemma₀ @(BlockSize alg) @n
    , Dict ← lemma₁
        @(BlockSize alg)
        @n
        @(2 ^ SizeBits alg)
        @(2 * BlockSize alg)
    = Dict
   where
    lemma₀ ∷
      ∀ (a ∷ Nat) (b ∷ Nat).
      (1 ≤ b, Mod a b ~ 0) ⇒
      Dict (b ≤ a)
    lemma₀ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

    lemma₁ ∷
      ∀ (a ∷ Nat) (b ∷ Nat) (c ∷ Nat) (d ∷ Nat).
      (b ≤ a, d ≤ Div c a) ⇒
      Dict (d ≤ Div c b)
    lemma₁ = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

  fact₁ ∷ Dict (DDiv (2 ^ SizeBits alg) n ~ Div (2 ^ SizeBits alg) n)
  fact₁
    | SHAFacts{} ← knownSHA @alg
    , Dict ← timesMod
        @(BlockSize alg)
        @(Div (2 ^ SizeBits alg) (BlockSize alg))
        @n
    , Dict ← lemma₀ @n
    , Dict ← condDivEqDDivFact @(2 ^ SizeBits alg) @n
    = Dict
   where
    lemma₀ ∷
      ∀ (a ∷ Nat).
      1 ≤ a ⇒
      Dict (Mod 0 a ~ 0)
    lemma₀ = unsafeCoerce (Dict ∷ Dict (0 ~ 0))

-- don't use any dictionaries of 'Data.Constraint.Nat', as they suffer from
-- https://github.com/clash-lang/clash-compiler/issues/2376

timesMod ∷ ∀ a b c. 1 ≤ c ⇒ Dict (Mod (a * b) c ~ Mod (Mod a c * Mod b c) c)
timesMod = unsafeCoerce (Dict ∷ Dict (0 ~ 0))

leTrans ∷ ∀ (a ∷ Nat) (b ∷ Nat) (c ∷ Nat). (b ≤ c, a ≤ b) ⇒ Dict (a ≤ c)
leTrans = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

modBound ∷ ∀ m n. 1 ≤ n ⇒ Dict (Mod m n ≤ n)
modBound = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

sha ∷
  ∀ (alg ∷ SHA) (dom ∷ Domain) (n ∷ Nat).
  (KnownSHA alg, KnownDomain dom, HiddenClockResetEnable dom) ⇒
  (KnownNat n, 1 ≤ n, n ≤ BlockSize alg, Mod (BlockSize alg) n ~ 0) ⇒
  Div (BlockSize alg) n ≤ ScheduleCount alg ⇒
  Signal dom (Maybe (BitVector n, Maybe (Index (n + 1)))) →
  -- ^ Input stream for passing messages, where each message may be
  -- separated into multiple n-bit frames. The messages are only
  -- composed out of the 'Just' wrapped data values passed to the
  -- stream, i.e., any intermediate 'Nothing' values will be
  -- ignored. The first component of each 'Just' value contains the
  -- actual data frame, while the second component is used to indicate
  -- the end of a message. Once the end of a message is reached, the
  -- second component also holds the amount of *unused* bits that have
  -- been added as LSBs to align with the frame size @n@.
  --
  -- Note that all of the last frame's data bits can be marked as
  -- unused. In that case, the message already was terminated by the
  -- previous frame and the current frame only serves as an
  -- end-of-message indicator. The same way, all bits of the frame can
  -- be used via marking none of the bits as unused. This way, the
  -- user is free in the choice of message termination system he likes
  -- to apply.
  ( Signal dom (Maybe (BitVector (MessageDigestSize alg)))
    -- ^ The response stream providing a @Just messageDigest@ as soon as
    -- the hash has been computed (after arrival of a terminated
    -- message).
  , Signal dom
      ( (Vec (DDiv (BlockSize alg) n - 1) (BitVector n))
      , (Index (DDiv (BlockSize alg) n))
      , Bool
      , (MessageBlock alg)
      , Bool
      , Bool
      , HashBlock alg
      )
  , Signal dom (Maybe (Either () (BitVector n)))
  )
sha inp
  = (\(a,b) -> (a,b,padMsg))
    ( first (fmap (fmap toDigest) . toSignal)
    $ second
        (\(a,b,c,d,e,f,g) → bundle
          ( toSignal a
          , toSignal b
          , toSignal c
          , toSignal d
          , toSignal e
          , toSignal f
          , toSignal g
          )
        )
    $ hashStream @alg
    $ fromSignal padMsg
    )
 where
  padMsg = padMessageStream @alg inp

  toDigest ∷ HashBlock alg → BitVector (MessageDigestSize alg)
  toDigest
    | SHAFacts _ ← knownSHA @alg
    = truncateB @_ @_
        @(MessageBlockWords alg * WordSize alg - MessageDigestSize alg)
    . concatBitVector#
