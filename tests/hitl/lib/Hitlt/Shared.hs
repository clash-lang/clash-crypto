module Hitlt.Shared
  ( Byte
  , ByteSize
  , Q
  , StackSize
  , StackValueSize
  , StackPadding
  , isReadyIndicator
  )
where

import Clash.Prelude

import Clash.Crypto.ECDSA.Modulo (ModSize)
import Clash.Crypto.Calculator.ISA

type Byte = BitVector 8
type ByteSize a = BitSize a `Div` BitSize Byte

-- | The prime used by the @SECP256@ curve of the FIDO protocol.
type Q =
  115792089210356248762697446949407573530086143415290314195533631308867097853951

-- | The indicator byte being send out initially for signalling the
-- host that the device is ready now.
isReadyIndicator :: Byte
isReadyIndicator = 0xAB

-- | Related to the stack
type StackSize = 50
type StackValueSize = 13
type StackPadding =
  BitSize Byte
    - BitSize (Maybe (Unsigned StackValueSize), Index (StackSize + 1))
        `Mod` BitSize Byte
