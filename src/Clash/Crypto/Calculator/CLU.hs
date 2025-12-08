{-|
Module      : Clash.Sized.Stack
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

The Cryptographic Logic Unit (CLU).
-}

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UndecidableInstances #-}

module Clash.Crypto.Calculator.CLU where

import Clash.Prelude hiding (Mod, Bit, unzip)

import Control.Arrow (second)
import Data.Bifunctor (bimap)
import Data.Constraint.Nat.Extra (LeTrans, CLog2Monotone)
import GHC.TypeNats.Proof (Rewrite(..), using)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.ECDSA.InverseModulo (fltCtmiE)
import Clash.Crypto.ECDSA.Karatsuba (karatsubaSequentialGated)
import Clash.Crypto.ECDSA.Modulo
  ( Mod, ModSize, computeModuloUnsigned, createMod, unMod
  )
import Clash.Signal.Channel (Channel, delayC, guardC, unzipC)

data CluInstruction
  = Add -- ^ addition
  | Sub -- ^ substraction
  | Inv -- ^ inverse modulo
  | Mul -- ^ multiplication
  | Bit -- ^ test bit
  deriving (Generic, NFDataX, BitPack, Ord, Eq, Enum, Bounded, Show)

data ECPrime
  = SecP256Mod
  | SecP256Ord
  deriving (Generic, NFDataX, BitPack, Ord, Eq, Enum, Bounded, Show)

type family CPrime (p :: ECPrime) ∷ Nat where
  CPrime SecP256Mod
    = 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1
  CPrime SecP256Ord
    = (2 ^ 256) - (2 ^ 224) + 2 ^ 192 - 0x4319055258E8617B0C46353D039CDAAF

type CMod p = Mod (CPrime p)
type ECMod = CMod SecP256Mod

-- | The Cryptographic Logic Unit (CLU) executing the given operation
-- on the given operands, where for unary operations only the first
-- operand is taken into account.
--
-- The `regs` parameter fixes the size of the target dependent
-- multipliers that are utilized by the 'Mul' operation. The `stages`
-- parameter fixes the recursion depth of the Karatsuba-based
-- multiplication unit, which requires `3 ^ stages` to run.
--
-- TODO: `stages == 0` currently is combinational and won't require a
-- single cycle. Fix this.
clu ∷
  ∀ dom. HiddenClockResetEnable dom ⇒
  ∀ stages → KnownNat stages ⇒
  ∀ regs → KnownNat regs ⇒
  Channel dom (ECPrime, (CluInstruction, (ECMod, ECMod))) →
  Channel dom ECMod
clu stages regs (unzipC → (cp, input))
  =   whenPrime SecP256Mod outMod
  <|> whenPrime SecP256Ord outOrd
 where
  (outMod, mInMod) = clu# (SNat @(CPrime SecP256Mod)) input mOut
  (outOrd, mInOrd) = clu# (SNat @(CPrime SecP256Ord)) input mOut

  mIn = whenPrime SecP256Mod mInMod
    <|> whenPrime SecP256Ord mInOrd

  mOut = karatsubaSequentialGated stages regs mIn

  whenPrime ∷ ∀ a. ECPrime → Channel dom a → Channel dom a
  whenPrime s = guardC ((Just s ==) <$> cp.content)

clu# ∷
  ∀ q p dom.
  ( HiddenClockResetEnable dom, KnownNat q, KnownNat p
  , 3 ≤ p, p ≤ q, q ≤ 2 * p
  ) ⇒
  -- | prime field
  SNat p →
  -- | input
  Channel dom (CluInstruction, (Mod q, Mod q)) →
  -- | shared multiplier output
  Channel dom (Unsigned (2 * ModSize q)) →
  ( -- | output
    Channel dom (Mod q)
  , -- | shared multiplier input
    Channel dom (Unsigned (ModSize q), Unsigned (ModSize q))
  )
clu# SNat input mOut
  | Rewrite ← using @(LeTrans 3 p q)
  , Rewrite ← using @(CLog2Monotone p q)
  , Rewrite ← using @(LeTrans (ModSize p) (ModSize q) (2 * ModSize q))
  = let
      (output, mIn)
        = clu## (second (bimap toP toP) <$> input)
        $ computeModuloUnsigned @p
          mOut

      -- we know that `p` won't fit twice into `q`, hence switching to
      -- a smaller modulo field only comes at the price of a single
      -- comparison and a single subtraction
      toP :: Mod q -> Mod p
      toP = createMod . truncateB @Index @_ @(q - p) . unMod . \z →
        z - if z <= natToNum @(p - 1) then 0 else natToNum @p

      exU ∷ Unsigned (ModSize p) → Unsigned (ModSize q)
      exU = extend @_ @_ @(ModSize q - ModSize p)

      exM ∷ Mod p → Mod q
      exM = createMod . extend @_ @_ @(q - p) . unMod
    in
      (exM <$> output, bimap exU exU <$> mIn)

clu## ∷
  ∀ p dom.
  (HiddenClockResetEnable dom, KnownNat p, 3 ≤ p) ⇒
  -- | input
  Channel dom (CluInstruction, (Mod p, Mod p)) →
  -- | shared multiplier with modulo output
  Channel dom (Mod p) →
  ( -- | output
    Channel dom (Mod p)
  , -- | shared multiplier with modulo input
    Channel dom (Unsigned (ModSize p), Unsigned (ModSize p))
  )
clu## input@(unzipC → (op, xy)) mOut
  = -- mux along all the possible operations
  (   whenOp Add (delayC (uncurry (+) <$> xy))
  <|> whenOp Sub (delayC (uncurry (-) <$> xy))
  <|> whenOp Bit (delayC (cluTestBit  <$> xy))
  <|> whenOp Inv (sndIfZero <$> delayC input <*> inv)
  <|> whenOp Mul mOut
  , -- only inverse modulo and multiplication modulo need the
    -- shared multiplier with modulo circuitry
      whenOp Inv xyInv
  <|> whenOp Mul (bimap bitCoerce bitCoerce <$> xy)
  )
 where
  (inv, xyInv) = fltCtmiE @p (fst <$> xy) mOut

  sndIfZero = \case
    (Inv, (0, y)) → const y
    _             → id

  cluTestBit (a, j)
    | j < natToNum @(ModSize p), testBit a (fromEnum j) = 1
    | otherwise = 0

  whenOp ∷ ∀ a. CluInstruction → Channel dom a → Channel dom a
  whenOp s = guardC ((Just s ==) <$> op.content)
