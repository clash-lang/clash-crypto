{-|
Module      : ISAPrint
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

A small demo application for printing a type level list of
instructions via UART. The main purpose of this application is to
check the resource usage of the type-level reification as a known
vector in hardware.
-}

{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}

module ISAPrint (topEntity) where

import Clash.Prelude hiding (print, Mod)
import Clash.Annotations.TH (makeTopEntity)
import Language.Haskell.Unicode (type (≤))

import Clash.Promoted.List
import Clash.Crypto.Calculator.ISA
import Clash.Crypto.Calculator.Modulo
import Clash.Crypto.ECDSA.Routines

import Hitl.Clash.Cores.Uart (uart)
import Hitl.Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom24)
import Hitl.Clash.Cores.LatticeSemi.ECP5.Pll (orangePll24)

-- allows to select the UART baud via a CPP define
#ifndef HITLT_BAUD
type BAUD = 9600
#else
type BAUD = HITLT_BAUD
#endif

type I group routine prime = Instr
  group (RepetitionBound routine) (RequiredStackSize routine) (Mod prime)

-- | State machine for printing a single instruction
isaPrint ∷
  ∀ {group}
    (dom ∷ Domain). HiddenClockResetEnable dom ⇒
  ∀ (prime ∷ Nat) → (KnownNat prime, 3 ≤ prime) ⇒
  ∀ (routine ∷ group) → KnownNat (RequiredStackSize routine) ⇒
  Signal dom (I group routine prime, Bool, Bool) →
  -- ^ (instruction, reset, step)
  Signal dom (Maybe (BitVector 8))
  -- ^ character to be sent via UART
isaPrint prime main = mealy (~~>)
  ( 0 ∷ Index 7
  , 0 ∷ Index (1 + Max (RequiredStackSize main) prime)
  )
 where
  _ ~~> (_, True, _    ) = ((0, 0), Nothing)
  s ~~> (i, _   , False) = (s, Just $ get i s)
  s ~~> (i, _   , True ) = (compute i s, Nothing)

  get i (n, v) = case i of
    PUT{} → case n of { 0 → 80 ; 1 → 85 ; 2 → 84 ; 3 → 32 ; _ → prV n v }
    POP{} → case n of { 0 → 80 ; 1 → 79 ; 2 → 80 ; 3 → 32 ; _ → prV n v }
    SWP{} → case n of { 0 → 83 ; 1 → 87 ; 2 → 80 ; 3 → 32 ; _ → prV n v }
    CUP{} → case n of { 0 → 67 ; 1 → 85 ; 2 → 80 ; 3 → 32 ; _ → prV n v }
    ADD{} → case n of { 0 → 65 ; 1 → 68 ; 2 → 68 ; 3 → 10 ; _ → 0 }
    SUB{} → case n of { 0 → 83 ; 1 → 85 ; 2 → 66 ; 3 → 10 ; _ → 0 }
    MUL{} → case n of { 0 → 77 ; 1 → 85 ; 2 → 76 ; 3 → 10 ; _ → 0 }
    INV{} → case n of { 0 → 73 ; 1 → 78 ; 2 → 86 ; 3 → 10 ; _ → 0 }
    BIT{} → case n of { 0 → 66 ; 1 → 73 ; 2 → 84 ; 3 → 32 ; _ → 0 }
    RUN{} → case n of
      0 → 82 ; 1 → 85 ; 2 → 78 ; 3 → 32 ; 4 → 82 ; 5 → 10 ; _ → 0

  prV n v = case n of
    4 → pack $ 48 + (resize @_ @_ @256 v `mod` 10)
    5 → 10
    _ → 0

  compute i (n, v)
    | n == 4, v > 9 = (n, v `div` 10)
    | n == 4        = (n + 1, 0)
    | n /= 0        = (n + 1, v)
    | otherwise     = (n + 1,  ) $ case i of
        PUT a → resize $ unMod a
        POP m → resize m
        SWP m → resize m
        CUP m → resize m
        _     → 0

topEntity ∷
  "CLK" ::: Clock Dom48 →
  "PMOD1_6" ::: Signal Dom24 Bit →
  "PMOD1_5" ::: Signal Dom24 Bit
topEntity (orangePll24 → (clk, rst)) rx = withClockResetEnable clk rst enableGen $
  let (_, tx, ack) = uart (SNat @BAUD) rx
                   $ mux (txReq .== Just 0 .||. n .== maxBound) (pure Nothing) txReq

      n = register (0 :: Index (Length (Instructions Main) + 1))
        $ mux upd ((+1) <$> n) n

      upd = n .< maxBound .&&. (txReq .== Just 0)

      reset = delay False upd
      step = isRising False ack

      txReq = isaPrint 11 Main $ bundle
        ( (instructions Main Main !!) <$> n
        , reset
        , step
        )

   in tx

makeTopEntity 'topEntity
