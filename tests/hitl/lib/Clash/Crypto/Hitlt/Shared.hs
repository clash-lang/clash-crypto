module Clash.Crypto.Hitlt.Shared (Byte, ByteSize, isReadyIndicator) where

import Clash.Prelude

type Byte = BitVector 8
type ByteSize a = BitSize a `Div` BitSize Byte

-- | The indicator byte being send out initially for signalling the
-- host that the device is ready now.
isReadyIndicator :: Byte
isReadyIndicator = 0xAB
