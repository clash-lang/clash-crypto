{-# OPTIONS_GHC -Wno-orphans #-}

module Clash.Crypto.Calculator.InverseModulo.Internal where

import Clash.Prelude

import GHC.TypeLits.KnownNat (KnownNat3 (natSing3), SNatKn (SNatKn), nameToSymbol)
import qualified Language.Haskell.TH as TH

import Clash.Crypto.Calculator.Modulo (ModSize)

-- This is a workaround using TH for type-level computations. Implementing
-- this computation as a type family works in simulation but not in synthesis.

type SictIterations m = 2 * ModSize m
type SictPrecompTyp m = ModInverse 2 m (m - SictIterations m - 1)

type family ModInverse (a ∷ Nat) (m ∷ Nat) (pow ∷ Nat) ∷ Nat

instance (KnownNat a, KnownNat m, KnownNat pow) ⇒
          KnownNat3 $(nameToSymbol ''ModInverse) a m pow
 where
  natSing3 = let a = natToNum @a
                 m = natToNum @m
                 pow = natToNum @pow ∷ Integer
                 calc 0 _ _ = 1
                 calc 1 val tmp = (val * tmp) `mod` m
                 calc n val tmp =
                  if even n then
                   calc (n `div` 2) (val * val `mod` m) (tmp `mod` m)
                  else
                   calc (n - 1) val ((tmp * val) `mod` m)
             in  SNatKn $ calc pow a 1
  {-# INLINE natSing3 #-}

class SictPrecompKnownNat (m ∷ Nat) where
 getSictPrecomp ∷ SNat m → Unsigned (ModSize m)

deriveSictPrecomp ∷
  ∀ (m ∷ Nat) → KnownNat m ⇒
  (1 <= m, 1 <= m - 2 * CLog 2 m, 2 * CLog 2 m <= m) ⇒
  TH.Q [TH.Dec]
deriveSictPrecomp m =
 let precompVal = lift (natToNum @(SictPrecompTyp m) ∷ Unsigned (CLog 2 m))
     mt = pure $ TH.LitT $ TH.NumTyLit $ natToNum @m
 in
 [d| instance SictPrecompKnownNat $mt where
        getSictPrecomp SNat = $precompVal |]
