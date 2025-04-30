{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}

module Modulo where

import Clash.Prelude

import Clash.Annotations.TH (makeTopEntity)
import Clash.Cores.UART (uart)
import Clash.Crypto.Hash.SHA (SHA(..))

import Domain (Dom48, Dom24)
import Pll (orangePll24)
import Clash.Crypto.ECDSA.Modulo (computeModuloPos, unMod)

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

type IntegerSize = 256
-- TODO: Once all PRs are merged, move this to one place.
type Q = 115792089210356248762697446949407573530086143415290314195533631308867097853951

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
  result = fmap unMod <$> computeModuloPos @Q @IntegerSize @_ @Dom24 s

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
