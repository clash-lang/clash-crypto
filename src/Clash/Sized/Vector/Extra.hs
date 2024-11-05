{-|
Module      : Clash.Sized.Vector.Extra
Copyright   : Copyright © 2024 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Some extra utility functions that extend the functionality of
'Clash.Sized.Vector'.
-}

module Clash.Sized.Vector.Extra
  ( (‼)
  ) where

import Clash.Prelude

-- | Sepecialized version of 'Clash.Sized.Vector.(!!)' that uses safe
-- bounds on the index with respect to the vector being accessed.
(‼) ∷ ∀ n a. KnownNat n ⇒ Vec n a → Index n → a
(‼) = (!!)
