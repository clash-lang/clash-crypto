{-|
Module      : Clash.Crypto.ECDSA.Fraction
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Hardware representation for fractions where the denominator is a power of 2.
-}

module Clash.Crypto.ECDSA.Fraction where
import Clash.Prelude

-- * Fractions of the form n/2^m.

-- Used in the FastGCD algorithm.

-- Only supports division by two (shifting).
-- The Index tracks where we are in the number (number of shifts to the right,
-- max of len + 1).
data HWFraction denMax len = HWFraction (Index denMax) (Signed (len + 1))
 deriving (Show, Eq, Generic, NFDataX)

shiftRFraction :: (KnownNat denMax, KnownNat len) =>
 HWFraction denMax len -> HWFraction denMax len
shiftRFraction (HWFraction n s) = HWFraction (n + 1) s

instance Resize (HWFraction denMax) where
  resize (HWFraction n s) = HWFraction n (resize s)
  zeroExtend (HWFraction n s) = HWFraction n (zeroExtend s)
  truncateB (HWFraction n s) = HWFraction n (truncateB s)

instance (KnownNat denMax, KnownNat len) => Num (HWFraction denMax len) where
  (+) :: HWFraction denMax len -> HWFraction denMax len -> HWFraction denMax len
  (HWFraction n s) + (HWFraction m t) =
   if n >= m -- First number has a bigger denominator
    then HWFraction n (s + shiftL t (fromEnum $ n - m))
    else HWFraction m (t + shiftL s (fromEnum $ m - n))
  (*) :: HWFraction denMax len -> HWFraction denMax len -> HWFraction denMax len
  (HWFraction n s) * (HWFraction m t) = HWFraction (n + m) (s * t)
  abs :: HWFraction denMax len -> HWFraction denMax len
  abs (HWFraction n s) = HWFraction n (abs s)
  signum :: HWFraction denMax len -> HWFraction denMax len
  signum (HWFraction _ s) = HWFraction 0 (signum s)
  fromInteger :: Integer -> HWFraction denMax len
  fromInteger = HWFraction 0 . fromInteger
  negate :: HWFraction denMax len -> HWFraction denMax len
  negate (HWFraction n s) = HWFraction n (negate s)
