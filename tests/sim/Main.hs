{-|
Module      : SHA
Copyright   : Copyright © 2024-2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Simulation Test Suite.
-}

import Prelude
import Test.Tasty

import qualified Simulate.Clash.Crypto.Calculator as Calculator
import qualified Simulate.Clash.Crypto.Calculator.CLU as CLU
import qualified Simulate.Clash.Crypto.Calculator.InverseModulo as InverseModulo
import qualified Simulate.Clash.Crypto.Calculator.Karatsuba as Karatsuba
import qualified Simulate.Clash.Crypto.Calculator.Modulo as Modulo
import qualified Simulate.Clash.Crypto.PubKey.ECDSA as ECDSA
import qualified Simulate.Clash.Crypto.PubKey.ECDSA.Nonce.Deterministic as Nonce
import qualified Simulate.Clash.Crypto.Hash.SHA as SHA
import qualified Simulate.Clash.Crypto.MAC.HMAC as HMAC
import qualified Simulate.Clash.Sized.Stack as Stack

main ∷ IO ()
main = defaultMain $ testGroup "clash-crypto simulation tests"
  [ Stack.tastyTests
  , SHA.tastyTests
  , HMAC.tastyTests
  , Karatsuba.tastyTests
  , Modulo.tastyTests
  , InverseModulo.tastyTests
  , CLU.tastyTests
  , Calculator.tastyTests
  , ECDSA.tastyTests
  , Nonce.tastyTests
  ]
