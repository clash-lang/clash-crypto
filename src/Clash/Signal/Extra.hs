{-|
Module      : Clash.Signal.Extra
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Some additional utility functions for memory control and signal
manipulations.
-}

{-# LANGUAGE Safe #-}

module Clash.Signal.Extra
  ( apWhen
  , regEnN
  ) where

import Data.Bool (Bool(..))
import Clash.Promoted.Nat (SNat(..), SNatLE(..), compareSNat, predSNat, leToPlus)
import Clash.Signal (Signal, HiddenClockResetEnable, mux, regEn)
import Clash.XException (NFDataX(..))
import Control.Applicative (Applicative(..), (<$>))
import Data.Function ((.), id)

-- | Updates a value inside an 'Applicative' context if and only if
-- the given Boolean condition evaluates to 'True' in the same
-- context.
apWhen ∷ Applicative f ⇒ f Bool → (a → a) → f a → f a
apWhen cond upd x = mux cond (upd <$> x) x

-- | A simple queuing FIFO that pushes data through whenever the
-- enable input line is high. Therefore, with every new input the
-- output at the end of the queue gets updated. It's nothing more than
-- a chain of 'regEn's in the end.
regEnN ∷
  ∀ dom a n.
  (HiddenClockResetEnable dom, NFDataX a) ⇒
  SNat n →
  -- ^ size of FIFO / number of stored elements
  a →
  -- ^ initial content of the FIFO
  Signal dom Bool →
  -- ^ "push next input" indicator
  Signal dom a →
  -- ^ input stream
  Signal dom a
  -- ^ final FIFO element
regEnN n@SNat initial en = case compareSNat n (SNat @0) of
  SNatGT → regEn initial en . leToPlus @1 @n (regEnN (predSNat n) initial en)
  SNatLE → id
