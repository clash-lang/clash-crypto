{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
module HMAC (topEntity, descape) where

import Clash.Prelude
import Clash.Annotations.TH (makeTopEntity)

import Clash.Cores.LatticeSemi.ECP5.Domain (Dom48, Dom24)
import Clash.Cores.LatticeSemi.ECP5.Pll (orangePll24)
import Clash.Crypto.Hitlt.Shared (Byte)
import Clash.Crypto.Hitlt.Uart (withUartRequestResponseHandler)

import Clash.Crypto.MAC.HMAC (hmac)
import Clash.Crypto.Hash.SHA (SHA(..))

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
  $ uncurry (hmac @SHAX) . descape

-- | We use `0x00` as an escape symbol to allow for changes in the
-- polarity of the indicator input
--
-- > 0x00 0   denotes `0x00`
-- > 0x00 1   triggers the "is key indicator" to be plulled 'low'
-- > 0x00 _   triggers the "is key indicator" to be plulled 'high '
descape ∷
  HiddenClockResetEnable dom ⇒
  Signal dom (Maybe Byte) →
  (Signal dom Bool, Signal dom (Maybe Byte))
descape = mealyB (~~>) (False, False)
 where
  (isKey, esc  ) ~~> Nothing   = ((isKey, esc  ), (isKey, Nothing  ))
  (isKey, False) ~~> Just 0x00 = ((isKey, True ), (isKey, Nothing  ))
  (isKey, False) ~~> Just byte = ((isKey, False), (isKey, Just byte))
  (isKey, True ) ~~> Just 0    = ((isKey, False), (isKey, Just 0x00))
  (_    , True ) ~~> Just 1    = ((False, False), (False, Nothing  ))
  (_    , True ) ~~> Just _    = ((True , False), (True , Nothing  ))

makeTopEntity 'topEntity
