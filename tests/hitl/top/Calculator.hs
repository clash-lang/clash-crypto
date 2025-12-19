{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}

module Calculator where

import Clash.Prelude hiding (Mod)
import Clash.Annotations.TH (makeTopEntity)
import Clash.Signal.Channel (cachedFromMaybe, newsfeed)

import Clash.Crypto.Calculator
import Clash.Crypto.Calculator.ISA

import Test.Clash.Crypto.Calculator (TestRoutines(..), TestIP)
import Hitl.Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom12)
import Hitl.Clash.Cores.LatticeSemi.ECP5.Pll (orangePll12)
import Hitl.Clash.Cores.Uart.Extra (bulkRead, withUartRequestResponseHandler)

-- allows to select the UART baud via a CPP define
#ifndef HITLT_BAUD
type BAUD = 9600
#else
type BAUD = HITLT_BAUD
#endif

topEntity ∷
  "CLK" ::: Clock Dom48 →
  "PMOD1_6" ::: Signal Dom12 Bit →
  "PMOD1_5" ::: Signal Dom12 Bit
topEntity (orangePll12 → (clk, rst))
  = withUartRequestResponseHandler clk rst (SNat @BAUD)
  $ newsfeed
      . calculator Main TestIP 2 72
      . cachedFromMaybe
      . bulkRead @(Vec 2 ECMod)

makeTopEntity 'topEntity
