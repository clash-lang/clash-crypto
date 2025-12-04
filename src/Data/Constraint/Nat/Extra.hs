{-|
Module      : Data.Constraint.Nat.Extra
Copyright   : Copyright © 2024-2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Some extra type families and properties for type level naturals.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -fplugin=GHC.TypeNats.Proof.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt=GHC.TypeNats.Proof.Plugin:VerifyProofs=False #-}

module Data.Constraint.Nat.Extra
  ( -- * Type Families
    DDiv
    -- * Proven Evidience
  , TimesMod
  , LeTrans
  , ModBound
  , CondMonotoneGE
  , TimesMonotoneRight
  , CancelMultiple
  , CancelFactor
  , MinOverLE
  , HalfIsLess
  , CLog2KeepsPositive
  , Div2RoundsDown
  , KeepsPositiveIfMultiple
  , DivisorIsLess
  , DivisorMonotoneInverse
  , ModZero
  , CLog2IsLessProduct
  , PositiveResultCond0
  , CLog2LECond0
  , CLog2Monotone
  ) where

import Clash.Prelude
import GHC.TypeNats.Proof

-- | Divisible division operation, which ensures that the dividend is
-- always a multiple of the divisor. Type family resolution will error
-- if the dividend is not a multiple of the divisor.
type DDiv ∷ Nat → Nat → Nat
type family DDiv n m where
  DDiv n m = If (n `Mod` m == 0)
    {- Then -}
      (n `Div` m)
    {- Else -}
      ( TypeError
          (    Text "n `DDiv` m requires n to be a multiple of m, "
          :<>: Text "which is not given for n = " :<>: ShowType n
          :<>: Text " and m = " :<>: ShowType m :<>: Text "."
          )
      )

instance
  ( 1 <= c
  ) ⇒ TimesMod a b c
class
  ( a * b `Mod` c ~ (a `Mod` c) * (b `Mod` c) `Mod` c
  ) ⇒ TimesMod a b c
-- ^ Evidence for
--
-- prop> ∀ a b c ∈ ℕ. c > 0 → (a · b) mod c ≡ ((a mod c) · (b mod c)) mod c
--
{-/ Proof (Coq): TimesMod
  Require Import Arith.
  Import Nat.
  intros a b c cpos.
  rewrite <- neq_0_le_1 in cpos.
  rewrite Div0.mul_mod_idemp_l.
  rewrite Div0.mul_mod_idemp_r.
  reflexivity.
/-}
instance TimesMod a b c ⇒ QED (TimesMod a b c)

instance
  ( a <= b, b <= c
  ) ⇒ LeTrans a b c
class
  ( a <= c
  ) ⇒ LeTrans a b c
-- ^ Evidence for
--
-- prop> ∀ a b c ∈ ℕ. a ≤ b ∧ b ≤ c → a ≤ c
--
{-/ Proof (Coq): LeTrans
  Require Import Arith.
  intros a b c H0 H1.
  apply (Nat.le_trans a b c H0 H1).
/-}
-- {-/ Proof (Agda): LeTrans
-- LeTrans _ _ _ = ≤-trans
-- /-}
instance LeTrans a b c ⇒ QED (LeTrans a b c)

instance
  ( 1 <= n
  ) ⇒ ModBound m n
class
  ( m `Mod` n <= n
  ) ⇒ ModBound m n
-- ^ Evidence for
--
-- prop> ∀ m n ∈ ℕ. n > 0 → m mod n ≤ n
--
{-/ Proof (Coq): ModBound
  Require Import Arith.
  Import Nat.
  intros m n npos.
  rewrite <- neq_0_le_1 in npos.
  generalize (mod_upper_bound m n npos) as H. intros.
  apply lt_le_incl in H. apply H.
/-}
instance ModBound m n ⇒ QED (ModBound m n)

instance
  ( 1 <= a, b <= c
  ) ⇒ TimesMonotoneRight a b c
class
  ( b <= a * c
  ) ⇒ TimesMonotoneRight a b c
-- ^ Evidence for
--
-- prop> ∀ a b c ∈ ℕ. a > 0 ∧ b ≤ c → b ≤ a · c
{-/ Proof (Coq): TimesMonotoneRight
  Require Import Arith.
  Import Nat.
  intros a b c apos H.
  (* eliminiate a = 0 case *)
  rewrite <- neq_0_le_1, neq_0_r in apos.
  destruct apos as [a1 apos]. rewrite apos. clear a apos.
  rewrite mul_succ_l.
  Search (_ <= _ + _).
  apply (add_le_mono 0 (a1 * c) b c (le_0_n (a1 * c)) H).
/-}
instance TimesMonotoneRight a b c ⇒ QED (TimesMonotoneRight a b c)

instance
  ( a <= b, a <= c
  ) ⇒ CondMonotoneGE a b c x
class
  ( a <= If x b c
  ) ⇒ CondMonotoneGE a b c x
-- ^ Evidence for
--
-- prop> ∀ a b c ∈ ℕ, x ∈ 𝔹. a ≤ b ∧ a ≤ c → a ≤ x ? b : c
--
{-/ Proof (Coq): CondMonotoneGE
  intros a b c x Hb Hc.
  case x.
  - apply Hb.
  - apply Hc.
/-}
instance CondMonotoneGE a b c x => QED (CondMonotoneGE a b c x)

instance
  ( 1 <= b, a `Mod` b ~ 0
  ) ⇒ CancelMultiple a b
class
  ( (a `Div` b) * b ~ a
  ) ⇒ CancelMultiple a b
-- ^ Evidence for
--
-- prop> ∀ a b ∈ ℕ. a mod b ≡ 0 → (a div b) · b ≡ a
--
{-/ Proof (Coq): CancelMultiple
  Require Import Arith.
  Import Nat.
  intros a b bpos H.
  rewrite <- neq_0_le_1 in bpos.
  rewrite Div0.mod_divides in H. destruct H as [n H]. rewrite H. clear a H.
  replace (b * n / b) with (n * b / b) by now rewrite mul_comm.
  rewrite (div_mul n b bpos), mul_comm. reflexivity.
/-}
instance CancelMultiple a b ⇒ QED (CancelMultiple a b)

instance
  ( 1 <= c * b, a `Mod` (c * b) ~ 0
  ) ⇒ CancelFactor a b c
class
  ( a `Div` (c * b) * c ~ a `Div` b
  ) ⇒ CancelFactor a b c
-- ^ Evidence for
--
-- prop> ∀ a b c ∈ ℕ. a mod (c · b) ≡ 0 → (a div (c · b)) · c ≡ a div b
--
{-/ Proof (Coq): CancelFactor
  Require Import Arith.
  Import Nat.
  intros a b c cbpos H.
  rewrite <- neq_0_le_1 in cbpos.
  generalize cbpos as cbpos'. intros.
  rewrite <- neq_mul_0 in cbpos'. destruct cbpos' as [cpos bpos].
  rewrite Div0.mod_divides in H. destruct H as [n H].
  rewrite !H. clear a H.
  replace (c * b * n)%nat with (n * (c * b))%nat by now rewrite mul_comm.
  rewrite (div_mul n (c * b) cbpos).
  replace (n * (c * b))%nat with ((n * c) * b)%nat by now rewrite mul_assoc.
  rewrite (div_mul (n * c) b bpos). reflexivity.
/-}
instance CancelFactor a b c ⇒ QED (CancelFactor a b c)

instance
  ( c <= a, c <= b
  ) ⇒ MinOverLE a b c
class
  ( c <= Min a b
  ) ⇒ MinOverLE a b c
-- ^ Evidence for
--
-- prop> ∀ a b c ∈ ℕ. c ≤ a ∧ c ≤ b → c ≤ min a b
--
{-/ Proof (Coq): MinOverLE
  Require Import Arith.
  intros a b c H0 H1.
  apply Nat.min_glb. apply H0. apply H1.
/-}
-- {-/ Proof (Agda): MinOverLE
-- MinOverLE _ _ zero _ _ = z≤n
-- MinOverLE _ _ (suc _) = ⊓-pres-m<
-- /-}
instance MinOverLE a b c ⇒ QED (MinOverLE a b c)

instance HalfIsLess n
class
  ( n `Div` 2 <= n
  ) ⇒ HalfIsLess n
-- ^ Evidence for
--
-- prop> ∀ n ∈ ℕ. n div 2 ≤ n
--
{-/ Proof (Coq): HalfIsLess
  Require Import Arith.
  intro n.
  rewrite <- Nat.div2_div.
  apply Nat.le_div2_diag_l.
/-}
instance HalfIsLess n ⇒ QED (HalfIsLess n)

instance
  ( 2 <= n
  ) ⇒ CLog2KeepsPositive n
class
  ( 1 <= CLog2 n
  ) ⇒ CLog2KeepsPositive n
-- ^ Evidence for
--
-- prop> ∀ n ∈ ℕ. n > 0 → clog₂ n > 0
--
{-/ Proof (Agda): CLog2KeepsPositive
open import Relation.Nullary.Negation.Core using (contradiction)
open import Data.Nat.Properties using (m+1+n≰m; ≤-trans; n≤1+n)

CLog2KeepsPositive n 2≤n = >-nonZero (lemma n 2≤n)
 where
  lemma : (n : ℕ) → 2 ≤ n → 1 ≤ ⌈log₂_⌉ n
  lemma (suc zero) 2≤n = contradiction (s≤s⁻¹ 2≤n) (m+1+n≰m 0)
  lemma (suc (suc zero)) 2≤n = s≤s z≤n
  lemma (suc (suc (suc n))) 2≤n =
    ≤-trans
      (lemma (suc (suc n)) (s≤s (s≤s z≤n)))
      (⌈log₂⌉-mono-≤ (n≤1+n ((suc (suc n)))))
/-}
instance CLog2KeepsPositive n ⇒ QED (CLog2KeepsPositive n)

instance Div2RoundsDown n
class
  ( n `Div` 2 <= n - (n `Div` 2)
  ) ⇒ Div2RoundsDown n
-- ^ Evidence for
--
-- prop> ∀ n ∈ ℕ. n div 2 ≤ n - (n div 2)
--
{-/ Proof (Coq): Div2RoundsDown
  Require Import Coq.Arith.Arith.
  Import Nat.
  intros n.
  apply (add_le_mono_l _ _ (n / 2)).
  rewrite add_sub_assoc.
  - rewrite (add_comm (n / 2) n), <- add_sub_assoc, sub_diag.
  rewrite <- (Nat.mul_1_l (n / 2)) at 1. rewrite <- mul_succ_l.
  rewrite add_0_r, div2_odd, div2_div.
  apply le_add_r.
  + trivial.
  - rewrite <- div2_div.
  apply le_div2_diag_l.
/-}
instance Div2RoundsDown n ⇒ QED (Div2RoundsDown n)

instance
  ( 1 <= n, 1 <= m, n `Mod` m ~ 0
  ) ⇒ KeepsPositiveIfMultiple n m
class
  ( 1 <= n `Div` m
  ) ⇒ KeepsPositiveIfMultiple n m
-- ^ Evidence for
--
-- prop> ∀ n m ∈ ℕ. n > 0 ∧ n mod m ≡ 0 → n div m > 0
--
{-/ Proof (Coq): KeepsPositiveIfMultiple
  Require Import Coq.Arith.Arith.
  Require Import Nat.
  Import Nat.
  intros n m npos mpos H.
  apply Div0.div_exact in H.
  apply neq_0_le_1 in npos.
  apply neq_0_le_1.
  rewrite H in npos.
  apply Nat.neq_mul_0 in npos.
  apply npos.
/-}
instance KeepsPositiveIfMultiple n m ⇒ QED (KeepsPositiveIfMultiple n m)

instance
  ( 1 <= n, 1 <= m, n `Mod` m ~ 0
  ) ⇒ DivisorIsLess n m
class
  ( m <= n
  ) ⇒ DivisorIsLess n m
-- ^ Evidence for
--
-- prop> ∀ n m ∈ ℕ. n > 0 ∧ n mod m ≡ 0 → m ≤ n
--
{-/ Proof (Coq): DivisorIsLess
  Require Import Arith.
  Import Nat.
  intros n m npos mpos H.
  (* eliminiate n = 0 case *)
  rewrite <- neq_0_le_1, neq_0_r in npos.
  destruct npos as [n1 npos]. rewrite npos in H. rewrite npos. clear n npos.
  (* eliminiate m = 0 case *)
  rewrite <- neq_0_le_1, neq_0_r in mpos.
  destruct mpos as [m1 mpos]. rewrite mpos in H. rewrite mpos. clear m mpos.
  rewrite Div0.mod_divides in H.
  destruct H as [k H]. destruct k.
  - contradict H. rewrite mul_comm. apply neq_succ_0.
  - rewrite H, mul_succ_r, add_comm. apply le_add_r.
/-}
instance DivisorIsLess n m ⇒ QED (DivisorIsLess n m)

instance
  ( 1 <= a, 1 <= b, b <= a, d <= c `Div` a
  ) ⇒ DivisorMonotoneInverse a b c d
class
  ( d <= c `Div` b
  ) ⇒ DivisorMonotoneInverse a b c d
-- ^ Evidence for
--
-- prop> ∀ a b c d ∈ ℕ. b ≤ a ∧ d ≤ c div a → d ≤ c div b
--
{-/ Proof (Coq): DivisorMonotoneInverse
  Require Import Arith.
  Import Nat.
  intros a b c d apos bpos H0 H1.
  (* eliminiate a = 0 case *)
  rewrite <- neq_0_le_1, neq_0_r in apos.
  destruct apos as [a1 apos]. rewrite apos in H1, H0. clear a apos.
  (* eliminiate b = 0 case *)
  rewrite <- neq_0_le_1, neq_0_r in bpos.
  destruct bpos as [b1 bpos]. rewrite bpos in H0. rewrite bpos. clear b bpos.
  destruct (div_le_compat_l c (S b1) (S a1)).
  - split. apply lt_0_succ. apply H0.
  - apply H1.
  - apply le_le_succ_r, (le_trans d (c / S a1) m H1 l).
/-}
instance DivisorMonotoneInverse a b c d ⇒ QED (DivisorMonotoneInverse a b c d)

instance
  ( 1 <= n
  ) ⇒ ModZero n
class
  ( 0 `Mod` n ~ 0
  ) ⇒ ModZero n
-- ^ Evidence for
--
-- prop> ∀ n ∈ ℕ. 0 mod n ≡ 0
--
{-/ Proof (Coq): ModZero
  Require Import Arith.
  intros. apply Nat.Div0.mod_0_l.
/-}
instance ModZero n ⇒ QED (ModZero n)

instance
  ( 1 <= m
  ) ⇒ CLog2IsLessProduct n m
class
  ( CLog 2 n <= n * m
  ) ⇒ CLog2IsLessProduct n m
-- ^ Evidence for
--
-- prop> ∀ n m ∈ ℕ. m > 0 → clog₂ n ≤ n · m
--
{-/ Proof (Agda): CLog2IsLessProduct
open import Relation.Binary.PropositionalEquality.Core using (sym)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; +-comm; m≤n⇒m≤n+o; m≤m*n; m^n≢0; ^-*-assoc; m≤n⇒m≤o+n)

CLog2IsLessProduct n (suc m)
  rewrite sym (⌈log₂2^n⌉≡n (n * (suc m)))
  rewrite sym (^-*-assoc 2 n (suc m))
  = ⌈log₂⌉-mono-≤
      (≤-trans (n≤2^n n)
        (m≤m*n (2 ^ n) ((2 ^ n) ^ m) {{m^n≢0 (2 ^ n) m {{m^n≢0 2 n}}}}))
 where
  1≤b∧a≤c⇒a+1≤b+c : (a b c : ℕ) → 1 ≤ b → a ≤ c → suc a ≤ b + c
  1≤b∧a≤c⇒a+1≤b+c a (suc b) c 1≤b a≤c = s≤s (m≤n⇒m≤o+n b a≤c)

  1≤2^n : (n : ℕ) → 1 ≤ 2 ^ n
  1≤2^n zero = ≤-refl
  1≤2^n (suc n)
    rewrite +-comm (2 ^ n) 0
    = m≤n⇒m≤n+o (2 ^ n) (1≤2^n n)

  n≤2^n : (n : ℕ) → n ≤ 2 ^ n
  n≤2^n zero = z≤n
  n≤2^n (suc n)
    rewrite +-comm (2 ^ n) 0
    = 1≤b∧a≤c⇒a+1≤b+c n (2 ^ n) (2 ^ n) (1≤2^n n) (n≤2^n n)
/-}
instance CLog2IsLessProduct n m ⇒ QED (CLog2IsLessProduct n m)

instance
  ( 1 <= b
  ) ⇒ PositiveResultCond0 a b
class
  ( 1 <= If (b <=? a) (a `Div` b + If (b `Mod` a <=? 0) 0 1) 1
  ) ⇒ PositiveResultCond0 a b
-- ^ Evidence for
--
-- prop> ∀ a b ∈ ℕ. b > 0 → b ≤ a ? a div b + (b mod a ≡ 0 ? 0 : 1) : 1
--
{-/ Proof (Coq): PositiveResultCond0
  Require Import Arith.
  Import Nat Div0.
  intros a b H0.
  destruct (b <=? a) eqn:H1. rewrite leb_le in H1.
  - case (b mod a <=? 0) eqn:H2.
    rewrite leb_le in H2. apply le_0_r, mod_divides in H2. destruct H2 as [c H2].
    rewrite H2 in H0, H1. rewrite H2. clear H2 b.
  -- destruct c as [|n].
  --- rewrite mul_comm in H0; simpl in H0.
      generalize (nle_succ_0 0). intros.
      contradiction.
  --- rewrite add_comm. simpl.
      rewrite mul_comm. simpl.
      destruct n as [|m].
  ---- rewrite add_comm. simpl.
       rewrite (div_same a).
       trivial. apply neq_0_le_1.
       rewrite mul_comm in H0. simpl in H0.
       rewrite add_comm in H0. simpl in H0.
       apply H0.
  ---- rewrite mul_comm in H1. simpl in H1.
       rewrite add_comm in H1.
       apply le_add_le_sub_r in H1. rewrite sub_diag in H1.
       apply le_0_r in H1. rewrite eq_add_0 in H1. destruct H1.
       rewrite H in H0. simpl in H0. generalize (nle_succ_0 0). intros.
       contradiction.
  -- apply le_add_l.
  - apply le_refl.
/-}
instance PositiveResultCond0 a b ⇒ QED (PositiveResultCond0 a b)

instance
  ( 1 <= a, 1 <= b
  ) ⇒ CLog2LECond0 a b
class
  ( CLog 2 ((2 ^ a) `Div` b)
      <= b * (If (b <=? a) (a `Div` b + If (b `Mod` a <=? 0) 0 1) 1)
  ) ⇒ CLog2LECond0 a b
-- ^ Evidence for
--
-- prop> ∀ a b ∈ ℕ. b > 0 → clog₂ (2ᵃ div b) ≤ b · (b ≤ a ? a div b + (b mod a ≤ 0 ? 0 : 1) ? 1)
--
{-/ Proof (Agda): CLog2LECond0
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Agda.Builtin.Unit using (tt)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality.Core using (sym; cong; subst)
open import Data.Nat.Divisibility using (∣⇒≤; m%n≡0⇒n∣m)
open import Relation.Nullary.Decidable.Core using (yes; no)

CLog2LECond0 a b
  rewrite sym (⌈log₂2^n⌉≡n
    (b * (if b ≤ᵇ a then a / b + (if b % a ≤ᵇ 0 then 0 else 1) else 1)))
  = ⌈log₂⌉-mono-≤ (lemma a b)
 where
  n≤m⇒2^n/[m+1]≤2^[m+1] : (n m : ℕ) → n ≤ m → 2 ^ n / (suc m) ≤ 2 ^ suc m
  n≤m⇒2^n/[m+1]≤2^[m+1] n zero      n≤0 rewrite n≤0⇒n≡0 n≤0 = s≤s z≤n
  n≤m⇒2^n/[m+1]≤2^[m+1] n m@(suc k) n≤m with n ≟ m
  ... | yes n≡m rewrite n≡m
      = let open ≤-Reasoning in begin
        2 ^ m / suc m ≤⟨ m/n≤m (2 ^ m) (suc m) ⟩
        2 ^ m         ≤⟨ ^-monoʳ-≤ 2 (n≤1+n m) ⟩
        2 ^ suc m     ∎
  ... | no n≢m
      = let open ≤-Reasoning in begin
        2 ^ n / suc m ≤⟨ /-monoʳ-≤ (2 ^ n) (n≤1+n m) ⟩
        2 ^ n / m     ≤⟨ n≤m⇒2^n/[m+1]≤2^[m+1] n k (s≤s⁻¹ (≤∧≢⇒< n≤m n≢m)) ⟩
        2 ^ m         ≤⟨ ^-monoʳ-≤ 2 (n≤1+n m) ⟩
        2 ^ suc m     ∎

  n≤m*[[n/m]+1] : (n m : ℕ) .{{_ : NonZero m}} → n ≤ m * suc (n / m)
  n≤m*[[n/m]+1] n m
    = let open ≤-Reasoning in begin
      n                 ≤⟨ ≤-reflexive (m≡m%n+[m/n]*n n m) ⟩
      n % m + n / m * m ≤⟨ +-monoˡ-≤ (n / m * m) (m%n≤n n m) ⟩
      m + (n / m * m)   ≡⟨ cong (m +_) (*-comm (n / m) m)  ⟩
      m + m * (n / m)   ≡⟨ sym (*-suc m (n / m)) ⟩
      m * suc (n / m)   ∎

  lemma :
    (n m : ℕ) .{{_ : NonZero n}} .{{_ : NonZero m}} →
    2 ^ n / m
      ≤ 2 ^ (m * (if m ≤ᵇ n then n / m + (if m % n ≤ᵇ 0 then 0 else 1) else 1))
  lemma n@(suc _) m@(suc k)
    with m ≤ᵇ n in m≤ᵇn?
  ... | false
      with m>n ← ≰⇒> (subst T m≤ᵇn? ∘ ≤⇒≤ᵇ)
      rewrite *-comm k 1
      rewrite +-comm k 0
      = n≤m⇒2^n/[m+1]≤2^[m+1] n k (s≤s⁻¹ m>n)
  ... | true
      with m≤n ← ≤ᵇ⇒≤ m n (subst T (sym m≤ᵇn?) tt)
      with m % n ≤ᵇ 0 in m%n≤ᵇ0?
  ...   | true
        with m%n≡0 ← n≤0⇒n≡0 (≤ᵇ⇒≤ _ _ (subst T (sym m%n≤ᵇ0?) tt))
        with n≡m ← ≤-antisym (∣⇒≤ (m%n≡0⇒n∣m m n m%n≡0)) m≤n
        rewrite cong pred n≡m
        rewrite n/n≡1 m {{_}}
        rewrite *-comm k 1
        rewrite +-comm k 0
        = m/n≤m (2 ^ m) m
  ...   | false
        rewrite +-comm (n / m) 1
        = let open ≤-Reasoning in begin
          2 ^ n / m             ≤⟨ m/n≤m (2 ^ n) m ⟩
          2 ^ n                 ≤⟨ ^-monoʳ-≤ 2 (n≤m*[[n/m]+1] n m) ⟩
          2 ^ (m * suc (n / m)) ∎
/-}
instance CLog2LECond0 a b ⇒ QED (CLog2LECond0 a b)

instance
  ( n <= m
  ) ⇒ CLog2Monotone n m
class
  ( CLog 2 n <= CLog 2 m
  ) ⇒ CLog2Monotone n m
-- ^ Evidence for
--
-- prop> ∀ n m ∈ ℕ. n ≤ m → clog₂ n ≤ clog₂ m
--
{-/ Proof (Agda): CLog2Monotone
CLog2Monotone m n = ⌈log₂⌉-mono-≤
/-}
instance CLog2Monotone a b ⇒ QED (CLog2Monotone a b)
