{-|
Module      : DerivePublicKey
Copyright   : Copyright © 2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

HITLT instance for 'Clash.Crypto.PubKey.ECDSA.DerivePublicKey'.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}

module ECDSADerivePublicKey where

import Clash.Prelude.Safe
import Clash.Annotations.TH (makeTopEntity)
import Clash.Signal.Channel (cachedFromMaybe, newsfeed)

import Clash.Crypto.Calculator
import Clash.Crypto.Calculator.ISA
import Clash.Crypto.Calculator.Modulo (ModSize)

import Hitl.Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom12)
import Hitl.Clash.Cores.LatticeSemi.ECP5.Pll (orangePll12)
import Hitl.Clash.Cores.Uart.Extra (bulkRead, withUartRequestResponseHandler)
import Hitl.Clash.Crypto.PubKey.ECDSA
import Clash.Crypto.PubKey.ECDSA

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
  $ newsfeed @(HitlCalculatorOutput DerivePublicKeyTest _)
      . fmap reverse
      . calculator DerivePublicKeyTest DerivePublicKeyIP 2 72
      . cachedFromMaybe
      . bulkRead @(HitlCalculatorInput DerivePublicKeyTest (ModSize SecP256ModPrime))

makeTopEntity 'topEntity
