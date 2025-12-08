{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}

module FastGCD (topEntity) where

import Clash.Prelude
import Clash.Annotations.TH (makeTopEntity)

import Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom12)
import Clash.Cores.LatticeSemi.ECP5.Pll (orangePll12)
import Clash.Signal.Channel (cachedFromMaybe, newsfeed)

import Clash.Crypto.ECDSA.InverseModulo (fastGcdSequential)

import Hitlt.Shared (Q)
import Hitlt.Uart (bulkRead, withUartRequestResponseHandler)

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
  $ newsfeed . fastGcdSequential @Q . cachedFromMaybe . bulkRead

makeTopEntity 'topEntity
