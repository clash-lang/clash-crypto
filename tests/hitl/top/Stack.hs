{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}

module Stack where

import Clash.Prelude
import Clash.Annotations.TH (makeTopEntity)

import Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom24)
import Clash.Cores.LatticeSemi.ECP5.Pll (orangePll24)
import Clash.Crypto.Hitlt.Uart (bulkRead, withUartRequestResponseHandler)

import Clash.Sized.Stack (stack)
import Clash.Sized.Stack (StackAction(..))
import Data.Maybe (isJust, fromMaybe)
import Clash.Crypto.Hitlt.Shared

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
  = withUartRequestResponseHandler clk rst (SNat @BAUD) $
   (\(bulkRead @(StackAction StackSize (Unsigned StackValueSize)) -> val) ->
   mux (isJust <$> register Nothing val)
       (Just <$>
        (minBound :: Unsigned StackPadding,) <$>
         stack (fromMaybe (Pop 0) <$> val))
       (pure Nothing))

makeTopEntity 'topEntity
