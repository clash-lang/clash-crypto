{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}

module Karatsuba where

import Clash.Prelude

import Clash.Annotations.TH (makeTopEntity)
import Clash.Cores.UART (uart)
import Clash.Crypto.Hash.SHA (SHA(..))

import Domain (Dom48, Dom24)
import Pll (orangePll24)
import Clash.Crypto.ECDSA.Karatsuba (karatsubaStreamingGated)

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

type IntegerSize = 128
type ResultSize = IntegerSize * 2

topEntity ∷
  "CLK" ::: Clock Dom48 →
  "PMOD1_6" ::: Signal Dom24 Bit →
  "PMOD1_5" ::: Signal Dom24 Bit
topEntity (orangePll24 → (clk24, rst24)) =
  withClockResetEnable clk24 rst24 enableGen top

top ∷
  HiddenClockResetEnable Dom24 ⇒
  Signal Dom24 Bit → Signal Dom24 Bit
top rx = tx
 where
  (rxData, tx, ack) = uart (SNat @BAUD) rx txReq

  s = bitCoerce <$> mealy bufferStep (0, def) rxData
  result = karatsubaStreamingGated @3 @36 @IntegerSize @IntegerSize @Dom24 s
  
  bufferStep ::
    (Index (IntegerSize `Div` 4 + 1), Vec (IntegerSize `Div` 4) (BitVector 8)) ->
    Maybe (BitVector 8) ->
    ((Index (IntegerSize `Div` 4 + 1), Vec (IntegerSize `Div` 4) (BitVector 8)), Maybe (Vec (IntegerSize `Div` 4) (BitVector 8)))
  bufferStep state Nothing = (state, Nothing)
  bufferStep (i, v) (Just val) =
    if i == maxBound then ((0,def), Just nv)
    else ((i + 1, nv), Nothing)
    where nv = v <<+ val

  txReq = mealyB (~~>)
    (def, 0 ∷ Index (ResultSize `Div` 8 + 1))
    (fmap toVec8 <$> result, ack)

  -- wait for the response from the crypto core
  s@(_, 0) ~~> (Nothing, _) = (s, Nothing)
  -- response received, start sending bytes
  (_, 0)   ~~> (Just h,  _) = ((h, maxBound), Just $ head h)
  -- wait for the UART ack of the byte previously sent
  s@(h, _) ~~> (_,   False) = (s, Just $ head h)
  -- UART ack received
  (h, n)   ~~> (_,    True) = ((h << d1, n - 1), Just $ head h)

  toVec8 ∷
    Unsigned ResultSize →
    Vec (ResultSize `Div` 8) (BitVector 8)
  toVec8 = bitCoerce

  v << n
    = fst $ shiftOutFrom0 n v

-- | We use `0x00` as an escape symbol to mark the end of the input
--
-- > 0x00 0b00000000   denotes `0x00` (no end marker)
-- > 0x00 0b???????1   marks the last byte with 7 bits used
-- > 0x00 0b??????10   marks the last byte with 6 bits used
-- > 0x00 0b?????100   marks the last byte with 5 bits used
-- > 0x00 0b????1000   marks the last byte with 4 bits used
-- > 0x00 0b???10000   marks the last byte with 3 bits used
-- > 0x00 0b??100000   marks the last byte with 2 bits used
-- > 0x00 0b?1000000   marks the last byte with 1 bits used
-- > 0x00 0b10000000   marks the previous byte to be the last byte
descape ∷
  HiddenClockResetEnable dom ⇒
  Signal dom (Maybe (BitVector 8)) →
  Signal dom (Maybe (BitVector 8, Maybe (Index 9)))
descape = mealy (~~>) False
 where
  esc   ~~> Nothing   = (esc, Nothing)
  False ~~> Just 0x00 = (True, Nothing)
  False ~~> Just byte = (False, Just (byte, Nothing))
  True  ~~> Just 0x00 = (False, Just (0x00, Nothing))
  True  ~~> Just byte = (False, Just (byte, Just $ trailingZeros + 1))
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

makeTopEntity 'topEntity
