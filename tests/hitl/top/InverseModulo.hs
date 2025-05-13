{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}

module InverseModulo where

import Clash.Prelude hiding (Mod)

import Clash.Annotations.TH (makeTopEntity)
import Clash.Cores.UART (uart)

import Domain (Dom48, Dom24)
import Pll (orangePll24)
import Clash.Crypto.ECDSA.Modulo (Mod(..), ModSize)
import Clash.Crypto.ECDSA.InverseModulo (bea)
import Clash.Crypto.ECDSA.Modulo (unMod)
import Data.Maybe (isJust, fromMaybe)

-- allows to select the UART baud via a CPP define
#ifndef HITLT_BAUD
type BAUD = 9600
#else
type BAUD = HITLT_BAUD
#endif

-- TODO: Once all PRs are merged, move this to one place.
type Q = 115792089210356248762697446949407573530086143415290314195533631308867097853951
type IntegerSize = ModSize Q

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

  toggleSwitch = isJust <$> dataLine
  toggle = register False $ mux toggleSwitch (not <$> toggle) toggle
  dataLine = fmap (Mod . bitCoerce) <$> mealy bufferStep (0, def) rxData
  dataReg = register 0 $ mux (isJust <$> dataLine) (fromMaybe 0 <$> dataLine) dataReg
  result = fmap (bitCoerce . unMod) <$> bea @Q @Dom24
    toggle dataReg

  bufferStep ::
    (Index (IntegerSize `Div` 8), Vec (IntegerSize `Div` 8) (BitVector 8)) ->
    Maybe (BitVector 8) ->
    ((Index (IntegerSize `Div` 8), Vec (IntegerSize `Div` 8) (BitVector 8)), Maybe (Vec (IntegerSize `Div` 8) (BitVector 8)))
  bufferStep state Nothing = (state, Nothing)
  bufferStep (i, v) (Just val) =
    if i == maxBound then ((0,def), Just nv)
    else ((i + 1, nv), Nothing)
    where nv = v <<+ val

  txReq = mealyB (~~>)
    (def, 0 ∷ Index (IntegerSize `Div` 8 + 1))
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
    Unsigned IntegerSize →
    Vec (IntegerSize `Div` 8) (BitVector 8)
  toVec8 = bitCoerce

  v << n
    = fst $ shiftOutFrom0 n v

makeTopEntity 'topEntity
