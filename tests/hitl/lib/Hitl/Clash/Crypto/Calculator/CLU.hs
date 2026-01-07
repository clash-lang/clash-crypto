module Hitl.Clash.Crypto.Calculator.CLU
 ( CluInput
 ) where

import Clash.Prelude

import Clash.Crypto.Calculator.ISA (CluInstruction, SecP256ModPrime)
import Clash.Crypto.Calculator.Modulo (ModSize)
import Hitl.Clash.Cores.Uart.Extra (Byte)

type CluInput =
  ( Unsigned (BitSize Byte - BitSize CluInstruction)
  , ( CluInstruction
    , ( (Unsigned (ModSize SecP256ModPrime), Unsigned (ModSize SecP256ModPrime))
      , Unsigned (ModSize SecP256ModPrime)
      )
    )
  )
