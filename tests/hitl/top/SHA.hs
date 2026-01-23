{-|
Module      : SHA
Copyright   : Copyright © 2024 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

HITLT instance for 'Clash.Crypto.Hash.SHA.sha'.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-deprecations #-}

module SHA (topEntity, descape) where

import Clash.Prelude.Safe
import Clash.Signal.Channel (newsfeed)
import Clash.Annotations.TH (makeTopEntity)

import Clash.Crypto.Hash.SHA (SHA(..), sha)

import Hitl.Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom24)
import Hitl.Clash.Cores.LatticeSemi.ECP5.Pll (orangePll24)
import Hitl.Clash.Cores.Uart.Extra (withUartRequestResponseHandler)
import Hitl.Clash.Crypto.Hash.Escape (descape)

-- allows to select an SHA variant via a CPP define
#ifndef HITLT_SHA
type SHAX = SHA256
#else
type SHAX = HITLT_SHA
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
  $ newsfeed . sha SHAX . descape

makeTopEntity 'topEntity
