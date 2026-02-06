{-|
Module      : Clash.Sized.Stack
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

The Cryptographic Logic Unit (CLU).
-}

module Clash.Crypto.Calculator.CLU where

import Clash.Prelude.Safe

import Clash.Crypto.Calculator.ISA (CluInstruction(..))

import Clash.Crypto.Calculator.InverseModulo (fltCtmiE)
import Clash.Crypto.Calculator.Karatsuba (karatsubaSequentialModulo)
import Clash.Signal.Channel (Channel, delayC, guardC, unzipC, zipRecent)

-- | The Cryptographic Logic Unit (CLU) executing the given operation
-- on the provided operands.
--
-- The @regBound@ parameter fixes the size of the target dependent
-- multipliers, as utilized by the 'Inv' and 'Mul' operations. The
-- @stages@ parameter fixes the recursion depth of the Karatsuba-based
-- multiplication unit.
--
-- The innermost tuple determines the two operands, paired with a
-- modulus defining the modulo field in which the operations are
-- executed. The operands are required to be smaller than the given
-- modulus. When using the 'Inv' operation, the modulus moreover is
-- required to be an odd prime. Passing zero as the modulus argument
-- selects the modulus @2^n@.
clu ∷
  ∀ n dom. (KnownNat n, HiddenClockResetEnable dom) ⇒
  ∀ stages → KnownNat stages ⇒
  ∀ regBound → KnownNat regBound ⇒
  Channel dom (CluInstruction, ((Unsigned n, Unsigned n), Unsigned n)) →
  Channel dom (Unsigned n)
clu stages regBound input@(unzipC → (op, xyk))
  =   delayC
  $   whenOp Inv (sndIfZero <$> delayC input <*> inv)
  <|> whenOp Mul mOut
  <|> guardC (simpleOp <$> op.content) (apOp <$> input)
 where
  (inv, xyInv) = fltCtmiE ((\((x,_), k) → (x, k)) <$> xyk) mOut

  mOut
    = karatsubaSequentialModulo stages regBound
    $   whenOp Inv (zipRecent (flip (,)) (snd <$> xyk) xyInv)
    <|> whenOp Mul xyk

  sndIfZero = \case
    (Inv, ((0, y), _)) → const y
    _                  → id

  apOp (Add, ((x, y), k))
    | k - x > y = x + y
    | otherwise = y - (k - x)

  apOp (Sub, ((x, y), k))
    | x >= y    = x - y
    | otherwise = k - (y - x)

  apOp (Bit, ((a, j), _))
    | j < natToNum @n, testBit a (fromEnum j) = 1
    | otherwise = 0

  apOp _ = undefined

  simpleOp = \case
    Just Add → True
    Just Sub → True
    Just Bit → True
    _ → False

  whenOp ∷ ∀ a. CluInstruction → Channel dom a → Channel dom a
  whenOp s = guardC ((Just s ==) <$> op.content)
