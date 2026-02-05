{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedRecordDot #-}

module DeterministicNonce (topEntity) where

import Clash.Prelude
import Clash.Annotations.TH (makeTopEntity)
import Hitl.Clash.Cores.LatticeSemi.ECP5.Domain
import Hitl.Clash.Cores.LatticeSemi.ECP5.Pll (orangePll24)
import Clash.Crypto.Hash.SHA (SHA(..), sha)
import Hitl.Clash.Crypto.Hash.Escape (descape)
import Hitl.Clash.Cores.Uart.Extra (withUartRequestResponseHandler)
import Clash.Crypto.ECDSA.DeterministicNonce (deriveNonce)
import Clash.Signal.Channel
import Clash.Crypto.Calculator.ISA (SecP256OrdPrime)
import Clash.Signal.DataStream (mapEnd)

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
  $ \b → let
    (result, shaInput)
     = deriveNonce SecP256OrdPrime SHAX
       (mapEnd (const ()) $ descape b)
       shaOutput
    shaOutput = sha SHAX shaInput
   in
    newsfeed result

makeTopEntity 'topEntity
