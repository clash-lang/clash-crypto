module Hitl.Clash.Crypto.Hash.Escape (descape) where

import Clash.Prelude
import Hitl.Clash.Cores.Uart.Extra (Byte)
import Clash.Signal.DataStream

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
    _ → Stretch

  frame = \case
    S   → Start ()
    M   → Middle
    E e → End e

  next = \case
    E{} → S
    _   → M

data NextExpectedDataFrame = S | M | E (Index (BitSize Byte))
  deriving (Generic, NFDataX)
