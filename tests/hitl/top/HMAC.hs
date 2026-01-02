{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
module HMAC (topEntity, descape) where

import Clash.Prelude

import Clash.Annotations.TH (makeTopEntity)
import Clash.Signal.Channel (newsfeed)
import Clash.Signal.DataStream (DataStream, Frame(..))

import Clash.Crypto.MAC.HMAC (hmac)
import Clash.Crypto.Hash.SHA (SHA(..), BlockSize)

import Hitl.Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom24)
import Hitl.Clash.Cores.LatticeSemi.ECP5.Pll (orangePll24)
import Hitl.Clash.Cores.Uart.Extra (Byte, withUartRequestResponseHandler)

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
  $ newsfeed . hmac SHAX . descape

-- | We use `0x00` as an escape symbol to allow for changes in the
-- polarity of the indicator input
--
-- > 0x00 0x00  denotes `0x00`
-- > 0x00 0xFF  denotes the next byte to be the last byte of the message
-- > 0x00 size  initates a new message with @size@ being the key size
descape ∷
  HiddenClockResetEnable dom ⇒
  Signal dom (Maybe Byte) →
  DataStream dom (Index ((BlockSize SHAX `Div` BitSize Byte) + 1)) () Byte
descape = mealy (~~>) (False, S 0 ∷ NextExpectedDataFrame)
 where
  (esc,   nef) ~~> Nothing   = ((esc,   nef     ), emptyFrame nef)
  (False, nef) ~~> Just 0x00 = ((True,  nef     ), emptyFrame nef)
  (False, nef) ~~> Just byte = ((False, next nef), frame nef byte)
  (True,  nef) ~~> Just 0x00 = ((False, next nef), frame nef 0x00)
  (True,  nef) ~~> Just 0xFF = ((False, E       ), emptyFrame nef)
  (True,  nef) ~~> Just byte = ((False, S byte  ), emptyFrame nef)

  frame = \case
    S x → Start $ unpack $ truncateB x
    M   → Middle
    E   → End ()

  next = \case
    E → S 0
    _ → M

  emptyFrame = \case
    S _ → Idle
    _   → NoData

data NextExpectedDataFrame = S Byte | M | E
  deriving (Generic, NFDataX)

makeTopEntity 'topEntity
