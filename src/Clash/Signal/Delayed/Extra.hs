{-|
Module      : Clash.Signal.Delayed.Extra
Copyright   : Copyright © 2024 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Some extra utility functions that extend the functionality of
'Clash.Signal.Delayed'.
-}

module Clash.Signal.Delayed.Extra
  ( dsFold
  ) where

import Clash.Prelude

import Data.Maybe (isJust)
import Language.Haskell.Unicode (type (≤))

-- | Temporally folds a signal over time. The folding function is
-- expected to take m-cycles and is assumed to only receive
-- ('Just'-wrapped) inputs with a temporal distance of at least @m@
-- cycles, i.e., there must be at least @m-1@ consecutive 'Nothing'
-- inputs between every two consecutive 'Just's.
--
-- A new round round of a fold is initiated via providing a
-- 'Just'-wrapped input, where every two consequitve 'Just'-wrapped
-- inputs must be at least @m@ cycles apart.

-- TODO: model the aformentioned assumptions as part of the type.
dsFold ∷
  ∀ (dom ∷ Domain) (b ∷ Type) (a ∷ Type) (k ∷ Nat) (m ∷ Nat).
  (HiddenClockResetEnable dom, NFDataX b, KnownNat m, 1 ≤ k + m) ⇒
  b →
  -- ^ initial value of the accumulator (only used after releasing the
  -- reset)
  (DSignal dom k (Maybe (a, b)) → DSignal dom (k + m) b) →
  -- ^ function / circuit to be folded
  DSignal dom k (Maybe a) →
  -- ^ input stream, where relevant inputs are 'Just'-wrapped
  DSignal dom (k + m) b
  -- ^ output stream
dsFold ival circuit input = result
 where
  result = case compareSNat @m @0 SNat SNat of
    SNatLE → acc
    SNatGT → mux (delayedI @m False (isJust <$> input))
               ( circuit
               $ (\i a → ( , a) <$> i)
                   <$> input
                   <*> antiDelay (SNat @m) acc
               )
               acc

  acc ∷ DSignal dom (k + m) b
  acc = delayedI @1 @b @dom @(k + m - 1) ival $ antiDelay d1 result
