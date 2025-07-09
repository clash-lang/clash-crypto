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
  , condMonotoneGE -- TODO: add 'If' support
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
  , cLog2IsLessProduct -- TODO: add 'If' support
  , positiveResultCond0 -- TODO: add 'If' support
  , cLog2LECond0 -- TODO: add 'If' support
  ) where

import Clash.Prelude

import Data.Type.Bool (If)
import Data.Type.Equality (type (==))
import Language.Haskell.Unicode (type (≤))
import Unsafe.Coerce (unsafeCoerce)
import GHC.TypeNats.Proof (Rewrite(..), QED)

{-/ Preamble (Coq):
Require Import Nat.
Require Import Arith Lia.
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
  TODO
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
  TODO
/-}
instance LeTrans a b c ⇒ QED (LeTrans a b c)

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
  TODO
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
  TODO
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
  ( a `Mod` b ~ 0
  ) ⇒ CancelMultiple a b
class
  ( a `Div` b * b ~ a
  ) ⇒ CancelMultiple a b
{-/ Proof (Coq): CancelMultiple
  TODO
/-}
instance CancelMultiple a b ⇒ QED (CancelMultiple a b)

-- | Evidence for
--
-- prop> ∀ a b c ∈ ℕ. a mod (c * b) ≡ 0 → (a div (c · b)) · c ≡ a div b
instance
  ( a `Mod` (c * b) ~ 0
  ) ⇒ CancelFactor a b c
class
  ( a `Div` (c * b) * c ~ a `Div` b
  ) ⇒ CancelFactor a b c
{-/ Proof (Coq): CancelFactor
  TODO
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
  TODO
/-}
instance MinOverLE a b c ⇒ QED (MinOverLE a b c)

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
  ) ⇒ CLog2KeepsPositive n
class
  ( 1 <= CLog 2 n
  ) ⇒ CLog2KeepsPositive n
{-/ Proof (Coq): CLog2KeepsPositive
  TODO
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
  TODO
/-}
instance Div2RoundsDown n ⇒ QED (Div2RoundsDown n)

-- | Evidence for
--
-- prop> ∀ n m ∈ ℕ. n > 0 ∧ n mod m ≡ 0 → n div m > 0
instance
  ( 1 <= n, n `Mod` m ~ 0
  ) ⇒ KeepsPositiveIfMultiple n m
class
  ( 1 <= n `Div` m
  ) ⇒ KeepsPositiveIfMultiple n m
{-/ Proof (Coq): KeepsPositiveIfMultiple
  TODO
/-}
instance KeepsPositiveIfMultiple n m ⇒ QED (KeepsPositiveIfMultiple n m)

-- | Evidence for
--
-- prop> ∀ n m ∈ ℕ. n > 0 ∧ n mod m ≡ 0 → m ≤ n
instance
  ( 1 <= n, n `Mod` m ~ 0
  ) ⇒ DivisorIsLess n m
class
  ( m <= n
  ) ⇒ DivisorIsLess n m
{-/ Proof (Coq): DivisorIsLess
  TODO
/-}
instance DivisorIsLess n m ⇒ QED (DivisorIsLess n m)

-- | Evidence for
--
-- prop> ∀ a b c d ∈ ℕ. b ≤ a ∧ d ≤ c div a → d ≤ c div b
instance
  ( b <= a, d <= c `Div` a
  ) ⇒ DivisorMonotoneInverse a b c d
class
  ( d <= c `Div` b
  ) ⇒ DivisorMonotoneInverse a b c d
{-/ Proof (Coq): DivisorMonotoneInverse
  TODO
/-}
instance DivisorMonotoneInverse a b c d ⇒ QED (DivisorMonotoneInverse a b c d)

-- | Evidence for
--
-- prop> ∀ n ∈ ℕ. 0 mod n ≡ 0
instance ModZero n
class
  ( 0 `Mod` n ~ 0
  ) ⇒ ModZero n
{-/ Proof (Coq): ModZero
  TODO
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
