{-# LANGUAGE UndecidableInstances #-}

module Clash.Crypto.ECDSA.Curves
 (Curve (..), CurveModulo)
where

import Data.Kind (Type)
import GHC.TypeLits

type Curve :: Type
data Curve = SECP256

type family CurveModulo (c :: Curve) where
 CurveModulo SECP256 = 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1
