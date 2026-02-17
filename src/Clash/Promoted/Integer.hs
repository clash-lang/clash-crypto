{-|
Module      : Clash.Promoted.List
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Recreates type level integers from type-level naturals via adding a sign.
-}

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE UndecidableInstances #-}

module Clash.Promoted.Integer
  ( ℤ
  , Toℤ
  , type (.+.)
  , type (.-.)
  , type (.*.)
  , Negate
  , Abs
  , SigNum
  , Negative
  , Inc
  , Dec
  , Minℤ
  , Maxℤ
  ) where

import Data.Bool (Bool(..))
import Data.Type.Bool (If)
import Data.Type.Ord (type (>=?), type (>?), Max)
import GHC.TypeNats (type (+), type (-), type (*), Nat)

-- | Type-level integers are type-level naturals with a sign.
type ℤ = (Bool, Nat)

-- | Converts a type-level natural into a type-level integer.
type Toℤ ∷ Nat → ℤ
type Toℤ n = '(False, n)

-- | Addition on type-level integers.
infixl 6 .+.
type (.+.) ∷ ℤ → ℤ → ℤ
type family x .+. y
 where
  '(False, x) .+. '(False, y) = '(False, x + y)
  '(True,  x) .+. '(True,  y) = '(True , x + y)
  '(False, x) .+. '(True,  y) = If (x >=? y) '(False, x - y) '(True , y - x)
  '(True,  x) .+. '(False, y) = If (x >?  y) '(True , x - y) '(False, y - x)

-- | Multiplication on type-level integers.
infixl 7 .*.
type (.*.) ∷ ℤ → ℤ → ℤ
type family x .*. y
 where
  '(False, x) .*. '(False, y) = '(False, x * y)
  '(False, x) .*. '(True,  y) = '(True , x * y)
  '(True,  x) .*. '(False, y) = '(True , x * y)
  '(True,  x) .*. '(True,  y) = '(False, x * y)

-- | Subtraction on type-level integers.
infixl 6 .-.
type (.-.) ∷ ℤ → ℤ → ℤ
type x .-. y = x .+. Negate y

-- | Negates a type-level integer.
type Negate ∷ ℤ → ℤ
type family Negate x
 where
  Negate '(True, y)  = '(False, y)
  Negate '(False, y) = '(True, y)

-- | Returns the absolute value of a type-level integer as type-level
-- natural.
type Abs ∷ ℤ → Nat
type family Abs x
 where
  Abs '(_, x) = x

-- | Returns the 'GHC.Num.signum' of a type level integer.
type SigNum ∷ ℤ → ℤ
type family SigNum x
 where
  SigNum '(_, 0) = '(False, 0)
  SigNum '(b, _) = '(b, 1)

-- | Returns @True@ if and only if the type-level integer is negative.
type Negative ∷ ℤ → Bool
type family Negative x
 where
  Negative '(b, _) = b

-- | Increments a type-level integer.
type Inc ∷ ℤ → ℤ
type Inc n = n .+. Toℤ 1

-- | Decrements a type-level integer.
type Dec ∷ ℤ → ℤ
type Dec n = n .-. Toℤ 1

-- | Returns the maximum of a type-level natural and a type-level
-- integer. The returned value will always be a type-level natural.
type Maxℤ ∷ Nat → ℤ → Nat
type family Maxℤ x y
 where
  Maxℤ x '(False, y) = Max x y
  Maxℤ x _ = x

-- | Returns the minimum of a type-level natural, representing a
-- negative number without its sign, and a type-level integer. The
-- returned value always will be a negative number, which however is
-- represented as a type-level natural without the sign.
type Minℤ ∷ Nat → ℤ → Nat
type family Minℤ x y
 where
  Minℤ x '(True , y) = Max x y
  Minℤ x _ = x
