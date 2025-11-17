{-|
Module      : Clash.Sized.Stack
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

The Cryptographic Logic Unit (CLU).
-}
module Clash.Crypto.Calculator.CLU where

import Clash.Prelude hiding (Mod, Bit)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.ECDSA.InverseModulo (fltCtmiE)
import Clash.Crypto.ECDSA.Karatsuba (karatsubaSequentialGated)
import Clash.Crypto.ECDSA.Modulo (Mod, ModSize, computeModuloUnsigned)
import Clash.Signal.Channel (Channel, content, delayC, guardC, zipC, unzipC, muxC)

data CluInstruction
  = Add -- ^ addition
  | Sub -- ^ substraction
  | Inv -- ^ inverse modulo
  | Mul -- ^ multiplication
  | Bit -- ^ test bit
  deriving (Generic, NFDataX, BitPack, Ord, Eq, Enum, Bounded, Show)

-- | The Cryptographic Logic Unit (CLU) executing the given operation
-- on the given operands, where for unary operations only the first
-- operand is taken into account.
--
-- The `regs` parameter fixes the size of target dependent multipliers
-- that are utilized by the 'Mul' operation and the `stages` parameter
-- fixes the recursion depth of the Karatsuba-based multiplication
-- unit such that the number of cycles the unit requires is equals `3
-- ^ stages`.
--
-- TODO: `stages == 0` currently is combinational and won't require a
-- single cycle. Fix this.
clu ∷
  forall dom p stages regs.
  (HiddenClockResetEnable dom, KnownNat p, 3 ≤ p) ⇒
  SNat stages →
  SNat regs →
  Channel dom (CluInstruction, (Mod p, Mod p)) →
  Channel dom (Mod p)
clu SNat SNat input@(unzipC → (op, unzipC → (x, y))) =
      withOp Add ( delayC $ (+) <$> x <*> y )
  <|> withOp Sub ( delayC $ (-) <$> x <*> y )
  <|> withOp Bit ( delayC $ cluTestBit <$> x <*> y )
  <|> withOp Inv ( secondIfZero <$> (delayC input) <*> inv )
  <|> withOp Mul mm
 where
  secondIfZero = \case
    (Inv, (0, z)) → const z
    _             → id

  (mmInv, inv) = fltCtmiE @p x mm

  mmInvInp = (\(a, b) → (bitCoerce a, bitCoerce b)) <$> mmInv

  mm = computeModuloUnsigned @p
     $ karatsubaSequentialGated @stages @regs
     $ muxC (op.content .== Just Inv) mmInvInp
     $ zipC (bitCoerce <$> x) (bitCoerce <$> y)

  withOp s = guardC ((Just s ==) <$> content op)

  cluTestBit ∷ Mod p → Mod p → Mod p
  cluTestBit a j
    | j < natToNum @(ModSize p), testBit a (fromEnum j) = 1
    | otherwise = 0
