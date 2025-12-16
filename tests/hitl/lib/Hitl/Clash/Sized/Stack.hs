module Hitl.Clash.Sized.Stack
  ( StackSize
  , StackValueSize
  , StackPadding
  ) where

import Clash.Prelude

import Hitl.Clash.Cores.Uart.Extra (Byte)

type StackSize = 50

type StackValueSize = 13

type StackPadding =
  BitSize Byte
    - BitSize (Maybe (Unsigned StackValueSize), Index (StackSize + 1))
        `Mod` BitSize Byte
