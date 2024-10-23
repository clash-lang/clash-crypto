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
  , dDivEqDiv
  , timesMod
  , leTrans
  , modBound
  , condMonotone
  , timesMonotoneRight
  , cancelMultiple
  , cancelFactor
  ) where

import Clash.Prelude

import Data.Constraint (Dict(..))
import Data.Type.Bool (If)
import Language.Haskell.Unicode (type (≤))
import Unsafe.Coerce (unsafeCoerce)

-- | Divisible division operation, which ensures that the dividend is
-- always a multiple of the divisor. Type family resolution will get
-- /stuck/ if the dividend is not a multiple of the divisor.
type DDiv ∷ Nat → Nat → Nat
type family DDiv a b where
  DDiv a b = DDivCheck (a `Mod` b) a b

-- | Helper type family for checking the reminder of
-- 'DDiv'. Unfortunately type families cannot be scoped.
type DDivCheck ∷ Nat → Nat → Nat → Nat
type family DDivCheck a b c where
  DDivCheck 0 a b = a `Div` b

-- | Evidence that if the dividend is a multiple of the of the
-- divisor, then 'DDiv' and 'Div' return the same result.
--
-- prop> ∀ a b ∈ ℕ. b > 0 ∧ a mod b ≡ 0 → a ddiv b ≡ a div b
dDivEqDiv ∷
  ∀ (a ∷ Nat) (b ∷ Nat).
  (1 ≤ b, a `Mod` b ~ 0) ⇒
  Dict (a `DDiv` b ~ a `Div` b)
dDivEqDiv =
  unsafeCoerce (Dict ∷ Dict (0 ~ 0))

-- Developers Note:
--
-- Don't use any dictionaries of 'Data.Constraint.Nat', as they suffer
-- from https://github.com/clash-lang/clash-compiler/issues/2376

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
-- prop> ∀ a b. a mod b ≡ 0 → (a div b) · b ≡ a
cancelMultiple ∷ ∀ (a ∷ Nat) (b ∷ Nat). a `Mod` b ~ 0 ⇒ Dict (a `Div` b * b ~ a)
cancelMultiple =
  unsafeCoerce (Dict ∷ Dict (0 ~ 0))

-- | Evidence for
--
-- prop> ∀ a b c. a mod (c * b) ≡ 0 → (a div (c · b)) · c ≡ a div b
cancelFactor ∷ ∀ (a ∷ Nat) (b ∷ Nat) (c ∷ Nat).
  a `Mod` (c * b) ~ 0 ⇒ Dict (a `Div` (c * b) * c ~ a `Div` b)
cancelFactor =
  unsafeCoerce (Dict ∷ Dict (0 ~ 0))
