{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
module KaratsubaModulo (topEntity) where

import Clash.Prelude
import Clash.Annotations.TH (makeTopEntity)
import Clash.Signal.Channel (cachedFromMaybe, newsfeed)

import Clash.Crypto.Calculator.ISA (SecP256ModPrime)
import Clash.Crypto.Calculator.Karatsuba (karatsubaSequentialModulo)
import Clash.Crypto.Calculator.Modulo (ModSize)

import Hitl.Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom24)
import Hitl.Clash.Cores.LatticeSemi.ECP5.Pll (orangePll24)
import Hitl.Clash.Cores.Uart.Extra (bulkRead, withUartRequestResponseHandler)

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
  = withUartRequestResponseHandler clk rst (SNat @BAUD)
  $ newsfeed
     . karatsubaSequentialModulo @(ModSize SecP256ModPrime) 3 40
     . fmap (, natToNum @SecP256ModPrime)
     . cachedFromMaybe
     . bulkRead

makeTopEntity 'topEntity
