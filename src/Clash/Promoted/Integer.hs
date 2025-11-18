{-|
Module      : Clash.Promoted.List
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Recreates type level integers from type-level naturals via adding a
sign.
-}

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoTemplateHaskell #-}
{-# LANGUAGE NoGeneralizedNewtypeDeriving #-}
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

type ℤ = (Bool, Nat)

type Toℤ ∷ Nat → ℤ
type Toℤ n = '(False, n)

infixl 6 .+.
type (.+.) ∷ ℤ → ℤ → ℤ
type family x .+. y
 where
  '(False, x) .+. '(False, y) = '(False, x + y)
  '(True,  x) .+. '(True,  y) = '(True , x + y)
  '(False, x) .+. '(True,  y) = If (x >=? y) '(False, x - y) '(True , y - x)
  '(True,  x) .+. '(False, y) = If (x >?  y) '(True , x - y) '(False, y - x)

infixl 7 .*.
type (.*.) ∷ ℤ → ℤ → ℤ
type family x .*. y
 where
  '(False, x) .*. '(False, y) = '(False, x * y)
  '(False, x) .*. '(True,  y) = '(True , x * y)
  '(True,  x) .*. '(False, y) = '(True , x * y)
  '(True,  x) .*. '(True,  y) = '(False, x * y)

infixl 6 .-.
type (.-.) ∷ ℤ → ℤ → ℤ
type x .-. y = x .+. Negate y

type Negate ∷ ℤ → ℤ
type family Negate x
 where
  Negate '(True, y)  = '(False, y)
  Negate '(False, y) = '(True, y)

type Abs ∷ ℤ → Nat
type family Abs x
 where
  Abs '(_, x) = x

type SigNum ∷ ℤ → ℤ
type family SigNum x
 where
  SigNum '(_, 0) = '(False, 0)
  SigNum '(b, _) = '(b, 1)

type Negative ∷ ℤ → Bool
type family Negative x
 where
  Negative '(b, _) = b

type Inc ∷ ℤ → ℤ
type Inc n = n .+. Toℤ 1

type Dec ∷ ℤ → ℤ
type Dec n = n .-. Toℤ 1

type Maxℤ ∷ Nat → ℤ → Nat
type family Maxℤ x y
 where
  Maxℤ x '(False, y) = Max x y
  Maxℤ x '(True , _) = x

type Minℤ ∷ Nat → ℤ → Nat
type family Minℤ x y
 where
  Minℤ x '(False, _) = x
  Minℤ x '(True , y) = Max x y
