{-|
Module      : Language.Haskell.Unicode
Copyright   : Copyright © 2024 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : stable
Portability : POSIX

Some useful Unicode symbol bindings, which are not already supported
by the @UnicodeSyntax@ extension yet.
-}

{-# LANGUAGE NoTemplateHaskell #-}
{-# LANGUAGE NoGeneralizedNewtypeDeriving #-}
{-# LANGUAGE Safe #-}

module Language.Haskell.Unicode
  ( type (≤)
  ) where

import Data.Type.Ord (type (<=))
import Data.Constraint (Constraint)

-- | Unicode version of the type level inequality constraint @<=@.
infix 4 ≤
type (≤) ∷ ∀ {n}. n → n → Constraint
type (≤) x y = (<=) x y
