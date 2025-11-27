{-# LANGUAGE UndecidableInstances #-}
{-|
Module      : Clash.Sized.Stack
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

A parameterized block RAM based stack supporting some additional
actions besides the usual push and pop, all of which run in a
single cycle.
-}

module Clash.Sized.Stack
  ( StackAction(..)
  , stack
  ) where

import Clash.Prelude

import Control.Monad (guard)
import Data.Maybe (fromMaybe)

-- | The possible actions for manipulating the stack.
data StackAction n a
  = Push a
  -- ^ pushes the given element to the top of the stack
  | Pop (Index (n + 1))
  -- ^ pops the given amount of elements from the top of the stack
  | Inspect (Index n)
  -- ^ inspects the n-th element (`0` being the top) without modifying
  -- the stack
  | CopyUp (Index n)
  -- ^ pushes a copy of the n-th element (`0` being the top) to the
  -- top of the stack
  | Swap (Index n)
  -- ^ swaps the n-th element on the stack with the top element
   deriving (Generic, NFDataX, Show)

instance (1 <= n, KnownNat n, BitPack a) => BitPack (StackAction n a) where

-- | A block RAM based stack supporting the given list of actions,
-- each always requiring a single cycle until its result appears on
-- the output. The inital output is `(Nothing, 0)`.
--
-- The term size refers to the fixed maximum size of the stack, whereas the
-- term charge refers to its current load. A full stack has a charge equal
-- to its size. A non-empty stack has a non-zero charge. An empty stack has
-- a null charge. The charge is always less than or equal to the size.
--
-- * PUSH: adds the given element to the stack unless the stack is
--   full. After a successful push, the output is `Just` the pushed
--   element. On failure, it is `Nothing`.
--
-- * POP: removes a given number of elements from the top of the stack.
--   If the argument is greater than the charge of the stack, the stack is
--   emptied, and the output is `Nothing`. Otherwise, the stack is non-empty
--   after operation, and the output is `Just` the value of the top element.
--
-- * INSPECT: inspects the n-th element on the stack. If `n` is strictly
--   less than the current charge, the output is `Just` the value of the
--   n-th element (`0` being the top). Otherwise, the output is `Nothing`.
--
-- * COPYUP: pushes a copy of the n-th element to the top of the
--   stack. If the stack is not full and `n` is strictly less than the
--   current charge, then the n-th element is copied to the top and
--   the output is `Just` the value of this element. Otherwise, nothing
--   happens and the output is `Nothing`.
--
-- * SWAP: swaps the n-th element on the stack with the top element.
--   If `n` is strictly less than the current charge, then the swap happens
--   and the output is `Just` the value of the top of the stack after
--   operation. Otherwise, nothing happens and the output is `Nothing`.
stack ∷
  ∀ dom n a.
  (HiddenClockResetEnable dom, NFDataX a, KnownNat n) ⇒
  Signal dom (StackAction n a) →
  -- ^ the stack action to be performed
  Signal dom (Maybe a, Index (n + 1))
  -- ^ The result of the action + the number of elements currently
  -- held by the stack.
stack stackAction = case toUNat (SNat @n) of
  -- the empty stack
  UZero → pure (Nothing, 0)

  -- the singleton stack
  USucc UZero → mealy (~~>) (Nothing, Just ()) stackAction
   where
    (Nothing, _) ~~> Push x   = ((Just x , Just ()), (Nothing, 0))
    (Nothing, _) ~~> _        = ((Nothing, Nothing), (Nothing, 0))
    (r      , c) ~~> Push{}   = ((r      , Nothing), (c >> r , 1))
    (r      , c) ~~> CopyUp{} = ((r      , Nothing), (c >> r , 1))
    (r      , c) ~~> Pop{}    = ((Nothing, Just ()), (c >> r , 1))
    (r      , c) ~~> _        = ((r      , Just ()), (c >> r , 1))

  -- any stack of size 2 or more
  USucc un@(USucc _) → result
   where
    (raddr, writeAct, result) = mealyB (~~>) (Nothing, 0, False, False)
      (stackAction, blockRamU NoClearOnReset (fromUNat un) raddr writeAct)

    (top, charge0, success0, wasInspect0) ~~> (action, val) =
      let
        top0 = fromMaybe val top
        rval = guard success0 >> Just (if wasInspect0 then val else top0)

        (charge1, success1) = case action of
          Inspect n → (charge0                  , charge0 > extend n)
          Swap n    → (charge0                  , charge0 > extend n)
          Pop n     → (satSub SatBound charge0 n, charge0 >        n)
          Push{}    → (satSucc SatBound charge0 , charge0 < maxBound)
          CopyUp n  → if charge0 > extend n
            then      (satSucc SatBound charge0 , charge0 < maxBound)
            else      (charge0                  , False             )

        top1 = case action of
          Push x   | success1        → Just x
          Pop n    | success1, n > 0 → Nothing
          CopyUp n | success1, n > 0 → Nothing
          Swap n   | success1, n > 0 → Nothing
          _                          → Just top0

        writeAction = guard success1 >> case action of
          Swap n | n > 0       → Just (toAddr    n, top0)
          Push{} | charge0 > 0 → Just (toAddr @n 0, top0)
          CopyUp{}             → Just (toAddr @n 0, top0)
          _                    → Nothing

        readAddr :: Index (n - 1)
        readAddr = case action of
          Push{}    → toAddr @n 0
          Pop n     → toAddr n
          Inspect n → toAddr n
          CopyUp n  → toAddr n
          Swap n    → toAddr n

        wasInspect1 = case action of
          Inspect n → n > 0
          _         → False
      in
        ( (top1, charge1, success1, wasInspect1)
        , (readAddr, writeAction, (rval, charge0))
        )
     where
      toAddr ∷ ∀ m. KnownNat m ⇒ Index m → Index (n - 1)
      toAddr = truncateB . satPred SatBound . satSub SatBound charge0 . resize
