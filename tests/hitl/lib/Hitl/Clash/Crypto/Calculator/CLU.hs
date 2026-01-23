{-|
Module      : Hitl.Clash.Crypto.Calculator.CLU
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Shared primitives for 'Clash.Crypto.Calculator.CLU'.
-}

module Hitl.Clash.Crypto.Calculator.CLU
 ( CluInput
 ) where

import Clash.Prelude.Safe

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
