{-|
Module      : Hitl.Clash.Sized.Stack
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Shared primitives for 'Clash.Sized.Stack'.
-}

{-# LANGUAGE Safe #-}

module Hitl.Clash.Sized.Stack
  ( StackSize
  , StackValueSize
  , StackPadding
  ) where

import Clash.Prelude.Safe

import Hitl.Clash.Cores.Uart.Extra (Byte)

type StackSize = 50

type StackValueSize = 13

type StackPadding =
  BitSize Byte
    - BitSize (Maybe (Unsigned StackValueSize), Index (StackSize + 1))
        `Mod` BitSize Byte
