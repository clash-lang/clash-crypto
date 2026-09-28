{-|
Module      : SHA3
Copyright   : Copyright © 2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

HITLT instance for 'Clash.Crypto.Hash.SHA3.Streaming.sha3'.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-deprecations #-}

module SHA3 (topEntity) where

import Clash.Prelude.Safe
import Clash.Annotations.TH (makeTopEntity)

import Clash.Signal.Channel (newsfeed)
import Clash.Crypto.Hash.SHA3.Types (SHA3(..))
import Clash.Crypto.Hash.SHA3.Streaming.Streaming (sha3)

import Hitl.Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom24)
import Hitl.Clash.Cores.LatticeSemi.ECP5.Pll (orangePll24)
import Hitl.Clash.Cores.Uart.Extra (withUartRequestResponseHandler)
import Hitl.Clash.Crypto.Hash.Escape (descape)

-- allows to select an SHA3 variant via a CPP define
#ifndef HITLT_SHA3
type SHAX = SHA3_256
#else
type SHAX = HITLT_SHA3
#endif

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
  $ newsfeed . sha3 SHAX . descape

makeTopEntity 'topEntity
