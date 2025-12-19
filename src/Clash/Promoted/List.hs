{-|
Module      : Clash.Promoted.List
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Type-level list operations.
-}

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoTemplateHaskell #-}
{-# LANGUAGE NoGeneralizedNewtypeDeriving #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE UndecidableInstances #-}

module Clash.Promoted.List
  ( InstanceAll
  , SortedList
  , Length
  , SLInsert
  , SLInsert#
  , SLMerge
  ) where

import Data.Kind (Constraint, Type)
import Data.Ord (Ordering(..))
import Data.Type.Ord (Compare)
import GHC.TypeNats (type (+), Nat)

-- | A type family for attaching a constraint to all elements in a
-- list. It is primarily used to ensure that all elements of a type
-- level list have instances for a certain class.
type InstanceAll ∷ [a] → (a → Constraint) → Constraint
type family InstanceAll xs c
 where
  InstanceAll '[]      _ = (() ∷ Constraint)
  InstanceAll (x : xr) c = (c x, InstanceAll xr c)

-- | Computes the length of the list
type Length ∷ [a] → Nat
type family Length xs
 where
  Length '[]      = 0
  Length (x : xr) = 1 + Length xr

-- | A type alias for sorted list. However, there is no mechanism in
-- place, which forces the list to actually be sorted.
type SortedList :: Type → Type
type SortedList a = [a]

-- | Inserts an element into a sorted list unless the element is
-- already in the list. Keeps the list sorted.
type SLInsert ∷ a → SortedList a → SortedList a
type family SLInsert x xs
 where
  SLInsert x '[]      = '[x]
  SLInsert x (y : yr) = SLInsert# (Compare x y) x y yr

-- | Internal helper for 'SLInsert'.
type SLInsert# ∷ Ordering → a → a → SortedList a → SortedList a
type family SLInsert# ord x y yr
 where
  SLInsert# LT x y yr = x : y : yr
  SLInsert# EQ _ y yr = y : yr
  SLInsert# GT x y yr = y : SLInsert x yr

-- | Merges to sorted list keeping the list sorted and deduplicating
-- its elements.
type SLMerge ∷ SortedList a → SortedList a → SortedList a
type family SLMerge xs ys
 where
  SLMerge xs       '[]      = xs
  SLMerge '[]      ys       = ys
  SLMerge (x : xr) (y : yr) = SLMerge# (Compare x y) x y xr yr

-- | Internal helper for 'SLMerge'.
type SLMerge# ∷ Ordering → a → a → SortedList a → SortedList a → SortedList a
type family SLMerge# ord x y xr yr
 where
  SLMerge# LT x y xr yr = x : SLMerge xr (y : yr)
  SLMerge# EQ x y xr yr = x : SLMerge xr yr
  SLMerge# GT x y xr yr = y : SLMerge (x : xr) yr
