{-|
Module      : Clash.Crypto.Calculator.Fraction
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Data types for fractions whose denominator is some power of
a constant related to the type.
-}

{-# LANGUAGE Safe #-}

module Clash.Crypto.Calculator.Fraction
  ( Frac2(..)
  , shiftRFrac2
  ) where

import Clash.Prelude.Safe

-- | Fractions of the form @n / 2ᵐ@. Only supporting division by two
-- via shifting.
data Frac2 (m ∷ Nat) (n ∷ Nat) = Frac2 (Index m) (Signed (n + 1))
  deriving (Show, Eq, Generic, NFDataX)

-- | Doubles the denominator.
shiftRFrac2 ∷
  (KnownNat m, KnownNat n) ⇒
  Frac2 m n →
  Frac2 m n
shiftRFrac2 (Frac2 m s) = Frac2 (m + 1) s

instance Resize (Frac2 m) where
  resize (Frac2 n s) = Frac2 n $ resize s
  zeroExtend (Frac2 n s) = Frac2 n $ zeroExtend s
  truncateB (Frac2 n s) = Frac2 n $ truncateB s

instance (KnownNat n, KnownNat m) ⇒ Num (Frac2 n m) where
  (Frac2 n s) + (Frac2 m t) =
   if n >= m -- First number has a bigger denominator
    then Frac2 n (s + shiftL t (fromEnum $ n - m))
    else Frac2 m (t + shiftL s (fromEnum $ m - n))
  (Frac2 n s) * (Frac2 m t) = Frac2 (n + m) (s * t)
  abs (Frac2 n s) = Frac2 n (abs s)
  signum (Frac2 _ s) = Frac2 0 (signum s)
  fromInteger = Frac2 0 . fromInteger
  negate (Frac2 n s) = Frac2 n (negate s)
