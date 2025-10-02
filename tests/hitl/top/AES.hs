{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
module AES (topEntity) where

import Clash.Prelude
import Clash.Annotations.TH (makeTopEntity)

import Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom12)
import Clash.Cores.LatticeSemi.ECP5.Pll (orangePll12)
import Clash.Crypto.Hitlt.Uart (bulkRead, withUartRequestResponseHandler)
import Clash.Signal.Channel (cachedFromMaybe, newsfeed)

import Clash.Crypto.Cipher.AES(AES(..), aesECBencryption)
-- allows to select an AES variant via a CPP define
#ifndef HITLT_AES
type AESX = AES128
#else
type AESX = HITLT_AES
#endif
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
  $ newsfeed . aesECBencryption @AESX . cachedFromMaybe . bulkRead

makeTopEntity 'topEntity
