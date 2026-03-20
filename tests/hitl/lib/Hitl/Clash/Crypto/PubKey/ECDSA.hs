module Hitl.Clash.Crypto.PubKey.ECDSA where

import Clash.Prelude.Safe
import Clash.Crypto.Calculator.ISA
import Clash.Crypto.PubKey.ECDSA

type SignHashTest        = SignHash        ∷ Routine Nat Nat SECP256R1
type DerivePublicKeyTest = DerivePublicKey ∷ Routine Nat Nat SECP256R1

type HitlCalculatorOutput r u = Vec (ResultCount r) (Unsigned u)
type HitlCalculatorInput  r u = Vec (ArgCount r)    (Unsigned u)
