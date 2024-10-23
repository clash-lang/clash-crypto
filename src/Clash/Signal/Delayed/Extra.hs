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

import Language.Haskell.Unicode (type (≤))

-- | Temporally folds a signal over time. The folding function is
-- allowed to introduce an m-cycle delay and is assumed to require the
-- inputs to be stable for at least @m@ cycles. 'dsFold' takes care
-- about satisifying the stability requirements for the accumulator,
-- but stability of the input stream needs the asserted outside of
-- 'dsFold', simiply for the reason of minimizing register usage, as
-- the latches for keeping the input streams stable also may be used
-- elsewhere.
--
-- A step trigger is used to start the next round of a fold, where
-- every two consequitve assertions the trigger must be at least @m@
-- cycles apart.

-- TODO: model the aformentioned assumptions as part of the type.
dsFold ∷
  ∀ (dom ∷ Domain) (b ∷ Type) (a ∷ Type) (k ∷ Nat) (m ∷ Nat).
  (HiddenClockResetEnable dom, NFDataX b, KnownNat m, 1 ≤ k + m) ⇒
  b →
  -- ^ initial value of the accumulator (only used after releasing the
  -- reset)
  DSignal dom (k + m) Bool →
  -- ^ step trigger
  (DSignal dom k b → DSignal dom k a → DSignal dom (k + m) b) →
  -- ^ function / circuit to be folded
  DSignal dom k a →
  -- ^ input stream
  DSignal dom (k + m) b
  -- ^ output stream
dsFold ival trg circuit is = result
 where
  result = dmux (circuit (antiDelay (SNat @m) acc) is) acc

  acc ∷ DSignal dom (k + m) b
  acc = delayedI @1 @b @dom @(k + m - 1) ival $ antiDelay d1 result

  dmux ∷ DSignal dom (k + m) b → DSignal dom (k + m) b → DSignal dom (k + m) b
  dmux = case compareSNat @m @0 SNat SNat of
    SNatLE → const
    SNatGT → mux trg
