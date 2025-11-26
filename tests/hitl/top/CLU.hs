{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}

module CLU where

import Clash.Prelude hiding (Mod)
import Clash.Annotations.TH (makeTopEntity)

import Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom24)
import Clash.Cores.LatticeSemi.ECP5.Pll (orangePll24)
import Clash.Crypto.Hitlt.Shared (Q)
import Clash.Crypto.Hitlt.Uart (bulkRead, withUartRequestResponseHandler)
import Clash.Signal.Channel (cachedFromMaybe, newsfeed)

import Clash.Crypto.ECDSA.Modulo (Mod)
import Clash.Crypto.Calculator.CLU (CluInstruction, clu)

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
      . clu @Dom24 @Q @3 @36 SNat SNat
      . cachedFromMaybe
      . fmap (snd <$>)
      . bulkRead @( Unsigned (8 - BitSize CluInstruction)
                  , (CluInstruction, (Mod Q, Mod Q))
                  )

makeTopEntity 'topEntity
