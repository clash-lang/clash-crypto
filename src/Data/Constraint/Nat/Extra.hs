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

module Data.Constraint.Nat.Extra
  ( DDiv
  , timesMod
  , leTrans
  , modBound
  , condMonotone
  , timesMonotoneRight
  , cancelMultiple
  , cancelFactor
  , maxDominates1
  , minOverLE
  ) where

import Clash.Prelude

import Data.Constraint (Dict(..))
import Data.Type.Bool (If)
import Data.Type.Equality (type (==))
import Language.Haskell.Unicode (type (≤))
import Unsafe.Coerce (unsafeCoerce)

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
timesMod ∷
  ∀ a b c. 1 ≤ c ⇒
  Dict (a * b `Mod` c ~ (a `Mod` c) * (b `Mod` c) `Mod` c)
timesMod =
  unsafeCoerce (Dict ∷ Dict (0 ~ 0))

-- | Evidence for
--
-- prop> ∀ a b c ∈ ℕ. a ≤ b ∧ b ≤ c → a ≤ c
leTrans ∷ ∀ (a ∷ Nat) (b ∷ Nat) (c ∷ Nat). (b ≤ c, a ≤ b) ⇒ Dict (a ≤ c)
leTrans =
  unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

-- | Evidence for
--
-- prop> ∀ m n ∈ ℕ. n > 0 → m mod n ≤ n
modBound ∷ ∀ m n. 1 ≤ n ⇒ Dict (m `Mod` n ≤ n)
modBound =
  unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

-- | Evidence for
--
-- prop> ∀ a b c ∈ ℕ. a > 0 ∧ b ≤ c → b ≤ a · c
timesMonotoneRight ∷ ∀ a b c. (1 ≤ a, b ≤ c) ⇒ Dict (b ≤ a * c)
timesMonotoneRight =
  unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

-- | Evidence for
--
-- prop> ∀ a b c ∈ ℕ, x ∈ 𝔹. a ≤ b ∧ a ≤ c → a ≤ x ? b : x
condMonotone ∷ ∀ a b c x. (a ≤ b, a ≤ c) ⇒ Dict (a ≤ If x b c)
condMonotone =
  unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

-- | Evidence for
--
-- prop> ∀ a b ∈ ℕ. a mod b ≡ 0 → (a div b) · b ≡ a
cancelMultiple ∷ ∀ (a ∷ Nat) (b ∷ Nat). a `Mod` b ~ 0 ⇒ Dict (a `Div` b * b ~ a)
cancelMultiple =
  unsafeCoerce (Dict ∷ Dict (0 ~ 0))

-- | Evidence for
--
-- prop> ∀ a b c ∈ ℕ. a mod (c * b) ≡ 0 → (a div (c · b)) · c ≡ a div b
cancelFactor ∷ ∀ (a ∷ Nat) (b ∷ Nat) (c ∷ Nat).
  a `Mod` (c * b) ~ 0 ⇒ Dict (a `Div` (c * b) * c ~ a `Div` b)
cancelFactor =
  unsafeCoerce (Dict ∷ Dict (0 ~ 0))

-- | Evidence for
--
-- prop> ∀ a b ∈ ℕ. b ≤ a → max a b ≡ a
maxDominates1 ∷ ∀ (a ∷ Nat) (b ∷ Nat).
  b ≤ a ⇒ Dict (Max a b ~ a)
maxDominates1 =
  unsafeCoerce (Dict ∷ Dict (0 ~ 0))

-- | Evidence for
--
-- prop> ∀ a b c ∈ ℕ. c ≤ a ∧ c ≤ b → c ≤ min a b
minOverLE ∷ ∀ (a ∷ Nat) (b ∷ Nat) (c ∷ Nat).
  (c ≤ a, c ≤ b) ⇒ Dict (c ≤ Min a b)
minOverLE =
  unsafeCoerce (Dict ∷ Dict (0 ≤ 0))
