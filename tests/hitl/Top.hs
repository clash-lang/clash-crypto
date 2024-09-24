{-# LANGUAGE UnicodeSyntax #-}
module Top where

import Clash.Prelude
import Control.Arrow
import Data.Bool

import Clash.Crypto.Hash.SHA

topEntity ∷
  HiddenClockResetEnable System ⇒
  Signal System (Maybe (BitVector 8, Bool)) →
  Signal System (Maybe (BitVector (MessageDigestSize SHA256)))
topEntity inp = sha @SHA256 @System @8
  $ fmap (fmap (second (bool Nothing $ Just maxBound))) inp
