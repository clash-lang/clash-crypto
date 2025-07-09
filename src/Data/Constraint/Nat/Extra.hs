{-|
Module      : Data.Constraint.Nat.Extra
Copyright   : Copyright © 2024 QBayLogic B.V.
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
  ( DDiv
  , TimesMod
  , LeTrans
  , ModBound
  , condMonotoneGE           -- TODO: add 'If' support
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
  , cLog2IsLessProduct       -- TODO: add 'If' support
  , positiveResultCond0      -- TODO: add 'If' support
  , cLog2LECond0             -- TODO: add 'If' support
  ) where

import Clash.Prelude

import Data.Type.Bool (If)
import Data.Type.Equality (type (==))
import Language.Haskell.Unicode (type (≤))
import Unsafe.Coerce (unsafeCoerce)
import GHC.TypeNats.Proof

{-/ Preamble (Agda):
open import Relation.Nullary.Negation.Core using (contradiction)
open import Data.Nat.Properties using (m+1+n≰m; ≤-trans; n≤1+n)
/-}

{-/ Preamble (Coq):
Require Import Nat.
Require Import Arith.
/-}

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

-- Developers Note:
--
-- Don't use any dictionaries of 'Data.Constraint.Nat', as they suffer from
-- https://github.com/clash-lang/clash-compiler/issues/2376#issuecomment-2376326236

-- | Evidence for
--
-- prop> ∀ a b c ∈ ℕ. c > 0 → (a · b) mod c ≡ ((a mod c) · (b mod c)) mod c
instance
  ( 1 <= c
  ) ⇒ TimesMod a b c
class
  ( a * b `Mod` c ~ (a `Mod` c) * (b `Mod` c) `Mod` c
  ) ⇒ TimesMod a b c
{-/ Proof (Coq): TimesMod
  Import Nat.
  intros a b c cpos.
  rewrite <- neq_0_le_1 in cpos.
  rewrite Div0.mul_mod_idemp_l.
  rewrite Div0.mul_mod_idemp_r.
  reflexivity.
/-}
instance TimesMod a b c ⇒ QED (TimesMod a b c)

-- | Evidence for
--
-- prop> ∀ a b c ∈ ℕ. a ≤ b ∧ b ≤ c → a ≤ c
instance
  ( a <= b, b <= c
  ) ⇒ LeTrans a b c
class
  ( a <= c
  ) ⇒ LeTrans a b c
{-/ Proof (Coq): LeTrans
  intros a b c H0 H1.
  apply (Nat.le_trans a b c H0 H1).
/-}
instance LeTrans a b c ⇒ QED (LeTrans a b c)
-- {-/ Proof (Agda): LeTrans
-- LeTrans _ _ _ = ≤-trans
-- /-}

-- | Evidence for
--
-- prop> ∀ m n ∈ ℕ. n > 0 → m mod n ≤ n
instance
  ( 1 <= n
  ) ⇒ ModBound m n
class
  ( m `Mod` n <= n
  ) ⇒ ModBound m n
{-/ Proof (Coq): ModBound
  Import Nat.
  intros m n npos.
  rewrite <- neq_0_le_1 in npos.
  generalize (mod_upper_bound m n npos) as H. intros.
  apply lt_le_incl in H. apply H.
/-}
instance ModBound m n ⇒ QED (ModBound m n)

-- | Evidence for
--
-- prop> ∀ a b c ∈ ℕ. a > 0 ∧ b ≤ c → b ≤ a · c
instance
  ( 1 <= a, b <= c
  ) ⇒ TimesMonotoneRight a b c
class
  ( b <= a * c
  ) ⇒ TimesMonotoneRight a b c
{-/ Proof (Coq): TimesMonotoneRight
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

-- | Evidence for
--
-- prop> ∀ a b c ∈ ℕ, x ∈ 𝔹. a ≤ b ∧ a ≤ c → a ≤ x ? b : c
{-
instance
  ( a <= b, a <= c
  ) ⇒ CondMonotoneGE a b c x
class
  ( a <= If x b c
  ) ⇒ CondMonotoneGE a b c x
{-/ Proof (Coq): CondMonotoneGE
  TODO
/-}
instance CondMonotoneGE a b c x => QED (CondMonotoneGE a b c x)
-}

condMonotoneGE ∷ ∀ a b c x. (a ≤ b, a ≤ c) ⇒ Rewrite (a ≤ If x b c)
condMonotoneGE = unsafeCoerce (Rewrite ∷ Rewrite (0 ≤ 0))

-- | Evidence for
--
-- prop> ∀ a b ∈ ℕ. a mod b ≡ 0 → (a div b) · b ≡ a
instance
  ( 1 <= b, a `Mod` b ~ 0
  ) ⇒ CancelMultiple a b
class
  ( (a `Div` b) * b ~ a
  ) ⇒ CancelMultiple a b
{-/ Proof (Coq): CancelMultiple
  Import Nat.
  intros a b bpos H.
  rewrite <- neq_0_le_1 in bpos.
  rewrite Div0.mod_divides in H. destruct H as [n H]. rewrite H. clear a H.
  replace (b * n / b) with (n * b / b) by now rewrite mul_comm.
  rewrite (div_mul n b bpos), mul_comm. reflexivity.
/-}
instance CancelMultiple a b ⇒ QED (CancelMultiple a b)

-- | Evidence for
--
-- prop> ∀ a b c ∈ ℕ. a mod (c * b) ≡ 0 → (a div (c · b)) · c ≡ a div b
instance
  ( 1 <= c * b, a `Mod` (c * b) ~ 0
  ) ⇒ CancelFactor a b c
class
  ( a `Div` (c * b) * c ~ a `Div` b
  ) ⇒ CancelFactor a b c
{-/ Proof (Coq): CancelFactor
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

-- | Evidence for
--
-- prop> ∀ a b c ∈ ℕ. c ≤ a ∧ c ≤ b → c ≤ min a b
instance
  ( c <= a, c <= b
  ) ⇒ MinOverLE a b c
class
  ( c <= Min a b
  ) ⇒ MinOverLE a b c
{-/ Proof (Coq): MinOverLE
  intros a b c H0 H1.
  apply Nat.min_glb. apply H0. apply H1.
/-}
instance MinOverLE a b c ⇒ QED (MinOverLE a b c)
-- {-/ Proof (Agda): MinOverLE
-- MinOverLE _ _ zero _ _ = z≤n
-- MinOverLE _ _ (suc _) = ⊓-pres-m<
-- /-}

-- | Evidence for
--
-- prop> ∀ n ∈ ℕ. n div 2 ≤ n
instance HalfIsLess n
class
  ( n `Div` 2 <= n
  ) ⇒ HalfIsLess n
{-/ Proof (Coq): HalfIsLess
  intro n.
  rewrite <- Nat.div2_div.
  apply Nat.le_div2_diag_l.
/-}
instance HalfIsLess n ⇒ QED (HalfIsLess n)

-- | Evidence for
--
-- prop> ∀ n ∈ ℕ. n > 0 → clog₂ n > 0
instance
  ( 1 <= n
  , 2 <= n
  ) ⇒ CLog2KeepsPositive n
class
  ( 1 <= CLog2 n
  ) ⇒ CLog2KeepsPositive n
{-/ Proof (Agda): CLog2KeepsPositive
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

-- | Evidence for
--
-- prop> ∀ n ∈ ℕ. n div 2 ≤ n - (n div 2)
instance Div2RoundsDown n
class
  ( n `Div` 2 <= n - (n `Div` 2)
  ) ⇒ Div2RoundsDown n
{-/ Proof (Coq): Div2RoundsDown
  Import Nat Bool.
  intros n.
  destruct (n mod 2) as [|m] eqn:parity. intros.
  - rewrite Div0.mod_divides in parity.
    destruct parity as [m even]. rewrite even. clear n even.
    rewrite mul_comm, (div_mul m 2 (neq_succ_0 1)), !mul_succ_r, mul_comm.
    rewrite add_sub. apply le_n.
  - destruct m.
  -- generalize (Div0.div_mod n 2) as sep. intros. rewrite parity in sep.
     replace (n - _)%nat with (2 * (n / 2) + 1 - (n / 2))%nat
       by now rewrite <- sep.
     rewrite !mul_succ_l, add_comm.
     rewrite <- add_sub_assoc by now apply le_add_l.
     rewrite add_sub, add_succ_l.
     apply le_succ_diag_r.
  -- generalize (mod_upper_bound n 2 (neq_succ_0 1)) as H. intros.
     contradict H. rewrite parity, <- !succ_lt_mono. apply nlt_0_r.
/-}
instance Div2RoundsDown n ⇒ QED (Div2RoundsDown n)

-- | Evidence for
--
-- prop> ∀ n m ∈ ℕ. n > 0 ∧ n mod m ≡ 0 → n div m > 0
instance
  ( 1 <= n, 1 <= m, n `Mod` m ~ 0
  ) ⇒ KeepsPositiveIfMultiple n m
class
  ( 1 <= n `Div` m
  ) ⇒ KeepsPositiveIfMultiple n m
{-/ Proof (Coq): KeepsPositiveIfMultiple
  Import Nat.
  intros n m npos mpos H.
  (* eliminiate n = 0 case *)
  rewrite <- neq_0_le_1, neq_0_r in npos.
  destruct npos as [n1 npos]. rewrite npos in H. rewrite npos. clear n npos.
  (* eliminiate m = 0 case *)
  rewrite <- neq_0_le_1, neq_0_r in mpos.
  destruct mpos as [m1 mpos]. rewrite mpos in H. rewrite mpos. clear m mpos.
  destruct (div_le_lower_bound (S n1) (S m1) 1).
  - apply neq_succ_0.
  - rewrite Div0.mod_divides in H.
    rewrite mul_succ_r, mul_comm.
    destruct H as [k H]. destruct k.
  -- contradict H. rewrite mul_comm. apply neq_succ_0.
  -- rewrite H. apply le_n_S. rewrite mul_succ_r, add_assoc. apply le_add_l.
  - apply le_n.
  - apply le_1_succ.
/-}
instance KeepsPositiveIfMultiple n m ⇒ QED (KeepsPositiveIfMultiple n m)

-- | Evidence for
--
-- prop> ∀ n m ∈ ℕ. n > 0 ∧ n mod m ≡ 0 → m ≤ n
instance
  ( 1 <= n, 1 <= m, n `Mod` m ~ 0
  ) ⇒ DivisorIsLess n m
class
  ( m <= n
  ) ⇒ DivisorIsLess n m
{-/ Proof (Coq): DivisorIsLess
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

-- | Evidence for
--
-- prop> ∀ a b c d ∈ ℕ. b ≤ a ∧ d ≤ c div a → d ≤ c div b
instance
  ( 1 <= a, 1 <= b, b <= a, d <= c `Div` a
  ) ⇒ DivisorMonotoneInverse a b c d
class
  ( d <= c `Div` b
  ) ⇒ DivisorMonotoneInverse a b c d
{-/ Proof (Coq): DivisorMonotoneInverse
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

-- | Evidence for
--
-- prop> ∀ n ∈ ℕ. 0 mod n ≡ 0
instance
  ( 1 <= n
  ) ⇒ ModZero n
class
  ( 0 `Mod` n ~ 0
  ) ⇒ ModZero n
{-/ Proof (Coq): ModZero
  intros. apply Nat.Div0.mod_0_l.
/-}
instance ModZero n ⇒ QED (ModZero n)

-- | Evidence for
--
-- prop> ∀ n m ∈ ℕ. m > 0 → clog₂ n ≤ n * m
{-
instance
  ( 1 <= m
  ) ⇒ CLog2IsLessProduct n m
class
  ( CLog 2 n ≤ n * m
  ) ⇒ CLog2IsLessProduct n m
{-/ Proof (Coq): CLog2IsLessProduct
  TODO
/-}
instance CLog2IsLessProduct n m ⇒ QED (CLog2IsLessProduct n m)
-}

cLog2IsLessProduct ∷
  ∀ (n ∷ Nat) (m ∷ Nat).
  1 ≤ m ⇒
  Rewrite (CLog 2 n ≤ n * m)
cLog2IsLessProduct = unsafeCoerce (Rewrite ∷ Rewrite (0 ≤ 0))

-- | Evidence for
--
-- prop> ∀ a b ∈ ℕ. b > 0 → b ≤ a ? a div b + (b mod a ≡ 0 ? 0 : 1) : 1
{-
instance
  ( 1 <= b
  ) ⇒ PositiveResultCond0 a b
class
  ( 1 ≤ If (b <=? a) (a `Div` b + If (b `Mod` a <=? 0) 0 1) 1
  ) ⇒ PositiveResultCond0 a b
{-/ Proof (Coq): PositiveResultCond0
  TODO
/-}
instance PositiveResultCond0 a b ⇒ QED (PositiveResultCond0 a b)
-}

positiveResultCond0 ∷
  ∀ (a ∷ Nat) (b ∷ Nat).
  1 ≤ b ⇒
  Rewrite (1 ≤ If (b <=? a) (a `Div` b + If (b `Mod` a <=? 0) 0 1) 1)
positiveResultCond0 = unsafeCoerce (Rewrite ∷ Rewrite (0 ≤ 0))

-- | Evidence for
--
-- prop> ∀ a b ∈ ℕ. b > 0 →
--       clog₂ (2ᵃ div b) ≤ b * (b ≤ a ? a div b + (b mod a ≤ 0 ? 0 : 1) ? 1)
{-
instance
  ( 1 <= b
  ) ⇒ CLog2LECond0 a b
class
  ( CLog 2 ((2 ^ a) `Div` b)
      ≤ b * (If (b <=? a) (a `Div` b + If (b `Mod` a <=? 0) 0 1) 1)
  ) ⇒ CLog2LECond0 a b
{-/ Proof (Coq): CLog2LECond0
  TODO
/-}
instance CLog2LECond0 a b ⇒ QED (CLog2LECond0 a b)
-}

cLog2LECond0 ∷
  ∀ (a ∷ Nat) (b ∷ Nat).
  1 ≤ b ⇒
  Rewrite
    ( CLog 2 ((2 ^ a) `Div` b)
    ≤ b * (If (b <=? a) (a `Div` b + If (b `Mod` a <=? 0) 0 1) 1)
    )
cLog2LECond0 = unsafeCoerce (Rewrite ∷ Rewrite (0 ≤ 0))
