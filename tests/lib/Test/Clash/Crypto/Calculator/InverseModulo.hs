{-|
Module      : Test.Clash.Crypto.Calculator.InverseModulo
Copyright   : Copyright © 2025-2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Shared test infrastructure for
'Clash.Crypto.Calculator.InverseModulo'.
-}

module Test.Clash.Crypto.Calculator.InverseModulo where

import Clash.Prelude.Safe

import Data.Maybe (fromMaybe)

import Clash.Crypto.Calculator.Modulo (PrimeField)
import Data.Modular (Modulus, inv, toMod, unMod)

-- | A golden reference from 'Data.Modular' for the inverse modulo
-- operation over different prime fields.
invMod ∷ ∀ p. Modulus p ⇒ PrimeField p → PrimeField p
invMod 0 = 0
invMod x
  = fromInteger
  $ unMod
  $ fromMaybe moduloError
  $ inv
  $ toMod @p
  $ toInteger x
 where
  moduloError =
    error "The inverse always exists in a prime field."
