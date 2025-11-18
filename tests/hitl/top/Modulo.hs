{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
module Modulo (topEntity) where

import Clash.Prelude
import Clash.Annotations.TH (makeTopEntity)

import Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom24)
import Clash.Cores.LatticeSemi.ECP5.Pll (orangePll24)
import Clash.Crypto.Hitlt.Uart (bulkRead, withUartRequestResponseHandler)
import Clash.Signal.Channel (cachedFromMaybe, newsfeed)
import Clash.Crypto.ECDSA.Modulo (computeModuloUnsigned)
import Clash.Crypto.ECDSA.Curves (Curve (SECP256), CurveModulo)

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
  $ newsfeed . computeModuloUnsigned @(CurveModulo SECP256) @256 . cachedFromMaybe . bulkRead

makeTopEntity 'topEntity
