module Test.Clash.Crypto.Calculator.InverseModulo where

import Clash.Prelude
import Data.Maybe (fromMaybe)

import qualified Clash.Crypto.Calculator.Modulo as Crypto
import qualified Data.Modular as Modular

invMod ∷ ∀ p. Modular.Modulus p ⇒ Crypto.Mod p → Crypto.Mod p
invMod 0 = 0
invMod x
  = fromInteger
  $ Modular.unMod
  $ fromMaybe moduloError
  $ Modular.inv
  $ Modular.toMod @p
  $ toInteger x
 where
  moduloError =
    error "The inverse always exists in a prime field."
