{-# LANGUAGE UnicodeSyntax #-}
module Top where

import Clash.Prelude

import Clash.Crypto.Hash.SHA

topEntity ∷
  HiddenClockResetEnable System ⇒
  Signal System (Maybe (BitVector 8, Maybe (Index 9))) →
  Signal System (Maybe (BitVector (MessageDigestSize SHA256)))
topEntity = sha @SHA256 @System @8
