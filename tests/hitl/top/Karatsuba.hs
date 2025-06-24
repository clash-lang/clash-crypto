{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
module Karatsuba (topEntity) where

import Clash.Prelude
import Clash.Annotations.TH (makeTopEntity)

import Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom24)
import Clash.Cores.LatticeSemi.ECP5.Pll (orangePll24)
import Clash.Crypto.Hitlt.Uart (bulkRead, withUartRequestResponseHandler)

import Clash.Crypto.ECDSA.Karatsuba (karatsubaSequentialGated)

import Data.Maybe (isJust)

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
  $ \(bulkRead → request) →
      let
        -- switch the toggle when a new value is received
        toggle = register False $ toggle ./=. (isJust <$> request)
        (x, y) = unbundle $ regMaybe def request
      in
        karatsubaSequentialGated @3 @36 @128 @128 toggle x y

makeTopEntity 'topEntity
