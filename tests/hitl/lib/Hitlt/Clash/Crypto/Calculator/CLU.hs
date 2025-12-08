module Hitlt.Clash.Crypto.Calculator.CLU
 ( CluInput
 ) where

import Clash.Prelude

import Clash.Crypto.Calculator.ISA (CluInstruction, ECMod)

import Hitlt.Shared (Byte)

type CluInput =
  ( Unsigned (BitSize Byte - BitSize CluInstruction)
  , ( CluInstruction
    , ( (Unsigned (BitSize ECMod), Unsigned (BitSize ECMod))
      , Unsigned (BitSize ECMod)
      )
    )
  )
