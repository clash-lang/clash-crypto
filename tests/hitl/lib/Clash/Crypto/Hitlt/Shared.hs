module Clash.Crypto.Hitlt.Shared (Byte, ByteSize, Q, isReadyIndicator) where

import Clash.Prelude

type Byte = BitVector 8
type ByteSize a = BitSize a `Div` BitSize Byte

-- | A prime that is utilized by multiple HITL tests.
type Q =
  115792089210356248762697446949407573530086143415290314195533631308867097853951

-- | The indicator byte being send out initially for signalling the
-- host that the device is ready now.
isReadyIndicator :: Byte
isReadyIndicator = 0xAB
