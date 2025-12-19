{-# LANGUAGE UndecidableInstances #-}

module Clash.Crypto.Hitlt.Shared
  ( Byte
  , ByteSize
  , Q
  , StackSize
  , StackValueSize
  , StackPadding
  , CluInput
  , isReadyIndicator
  , ECPrime(..)
  , CMod
  , ECMod
  , CPrime
  )
where

import Clash.Prelude

import qualified Clash.Crypto.ECDSA.Modulo as M (Mod, ModSize)
import Clash.Crypto.Calculator.CLU (CluInstruction)

type Byte = BitVector 8
type ByteSize a = BitSize a `Div` BitSize Byte

-- | The prime used by the @SECP256@ curve of the FIDO protocol.
type Q =
  115792089210356248762697446949407573530086143415290314195533631308867097853951

-- | The indicator byte being send out initially for signalling the
-- host that the device is ready now.
isReadyIndicator :: Byte
isReadyIndicator = 0xAB

data ECPrime
  = SecP256Mod
  | SecP256Ord
  deriving (Generic, NFDataX, BitPack, Ord, Eq, Enum, Bounded, Show)

type family CPrime (p :: ECPrime) ∷ Nat where
  CPrime SecP256Mod
    = 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1
  CPrime SecP256Ord
    = (2 ^ 256) - (2 ^ 224) + 2 ^ 192 - 0x4319055258E8617B0C46353D039CDAAF

type CMod p = M.Mod (CPrime p)
type ECMod = CMod SecP256Mod

-- | Related to the stack
type StackSize = 50
type StackValueSize = 13
type StackPadding =
  BitSize Byte
    - BitSize (Maybe (Unsigned StackValueSize), Index (StackSize + 1))
        `Mod` BitSize Byte

-- | Related to CLU
type CluInput =
  ( Unsigned (BitSize Byte - BitSize CluInstruction)
  , ( CluInstruction
    , ( (Unsigned (M.ModSize Q), Unsigned (M.ModSize Q))
      , Unsigned (M.ModSize Q)
      )
    )
  )
