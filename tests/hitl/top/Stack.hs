{-|
Module      : Stack
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

HITLT instance for 'Clash.Sized.Stack.stack'.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}

module Stack where

import Clash.Prelude.Safe
import Clash.Annotations.TH (makeTopEntity)
import Data.Maybe (fromMaybe)

import Clash.Sized.Stack (StackAction(Pop), stack)

import Hitl.Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom24)
import Hitl.Clash.Cores.LatticeSemi.ECP5.Pll (orangePll24)
import Hitl.Clash.Cores.Uart.Extra (bulkRead, withUartRequestResponseHandler)
import Hitl.Clash.Sized.Stack (StackPadding, StackSize, StackValueSize)

-- allows to select the UART baud via a CPP define
#ifndef HITLT_BAUD
type BAUD = 9600
#else
type BAUD = HITLT_BAUD
#endif

topEntity ∷
  "CLK" ::: Clock Dom48 →
  "PMOD1_6" ::: Signal Dom24 Bit →
  "PMOD1_5" ::: Signal Dom24 Bit
topEntity (orangePll24 → (clk, rst))
  = withUartRequestResponseHandler clk rst (SNat @BAUD) $
   (\(bulkRead @(StackAction StackSize (Unsigned StackValueSize)) → val) →
        (\v s → v >> pure (0 :: Unsigned StackPadding, s))
        <$> delay Nothing val
        <*> stack (fromMaybe (Pop 0) <$> val))

makeTopEntity 'topEntity
