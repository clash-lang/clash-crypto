{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wno-deprecations #-}

module SHA (topEntity) where

import Clash.Prelude
import Clash.Signal.Channel (newsfeed)
import Clash.Signal.DataStream (DataStream, Frame(..))
import Clash.Annotations.TH (makeTopEntity)

import Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom24)
import Clash.Cores.LatticeSemi.ECP5.Pll (orangePll24)

import Clash.Crypto.Hash.SHA (SHA(..), sha)

import Hitlt.Shared (Byte)
import Hitlt.Uart (withUartRequestResponseHandler)

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

-- | We use `0x00` as an escape symbol to mark the end of the input
--
-- > 0x00 0b00000000   denotes `0x00` (no end marker)
-- > 0x00 0b???????1   marks the next byte to be the last byte with 8 bits used
-- > 0x00 0b??????10   marks the next byte to be the last byte with 7 bits used
-- > 0x00 0b?????100   marks the next byte to be the last byte with 6 bits used
-- > 0x00 0b????1000   marks the next byte to be the last byte with 5 bits used
-- > 0x00 0b???10000   marks the next byte to be the last byte with 4 bits used
-- > 0x00 0b??100000   marks the next byte to be the last byte with 3 bits used
-- > 0x00 0b?1000000   marks the next byte to be the last byte with 2 bits used
-- > 0x00 0b10000000   marks the next byte to be the last byte with 1 bit used
descape ∷
  HiddenClockResetEnable dom ⇒
  Signal dom (Maybe Byte) →
  DataStream dom () (Index (BitSize Byte)) Byte
descape = mealy (~~>) (False, S ∷ NextExpectedDataFrame)
 where
  (esc,   nef) ~~> Nothing   = ((esc,   nef            ), emptyFrame nef)
  (False, nef) ~~> Just 0x00 = ((True,  nef            ), emptyFrame nef)
  (False, nef) ~~> Just byte = ((False, next nef       ), frame nef byte)
  (True,  nef) ~~> Just 0x00 = ((False, next nef       ), frame nef 0x00)
  (True,  nef) ~~> Just byte = ((False, E trailingZeros), emptyFrame nef)
   where
    trailingZeros
      | testBit byte 0 = 0
      | testBit byte 1 = 1
      | testBit byte 2 = 2
      | testBit byte 3 = 3
      | testBit byte 4 = 4
      | testBit byte 5 = 5
      | testBit byte 6 = 6
      | testBit byte 7 = 7
      | otherwise      = 8

  emptyFrame = \case
    S → Idle
    _ → NoData

  frame = \case
    S   → Start ()
    M   → Middle
    E e → End e

  next = \case
    E{} → S
    _   → M

data NextExpectedDataFrame = S | M | E (Index (BitSize Byte))
  deriving (Generic, NFDataX)

makeTopEntity 'topEntity
