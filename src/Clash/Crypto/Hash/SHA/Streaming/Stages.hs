{-|
Module      : Clash.Crypto.Hash.SHA.Streaming.Stages
Copyright   : Copyright © 2024 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Stage introduction for automatically aligning the computation stages
with the input rate resulting from the chosen input frame size.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Clash.Crypto.Hash.SHA.Streaming.Stages
  ( DistributedStages
  , atMostOnePerStage
  , distributeStages
  ) where

import Clash.Prelude

import Control.Monad
import Data.Constraint (Dict(..))
import Data.Constraint.Nat.Extra (leTrans)
import Data.Proxy (Proxy(..))
import Data.Type.Bool (type (&&), If)
import Data.Type.Equality (type (==))
import GHC.TypeLits.KnownNat (KnownNat3(..), SNatKn(..), nameToSymbol)
import Language.Haskell.Unicode (type (≤))
import Unsafe.Coerce (unsafeCoerce)

import qualified GHC.TypeNats as GHC (natVal)

-- | A type family for calculating the positions at which we need to
-- put a register in front, if we like to evenly distribute @d@
-- registers between a chain of @n@ circuit blocks, where @d < n@.
type DistributedStages ∷ Nat → Nat → Nat → Nat
type family DistributedStages n d i where
  DistributedStages _ 0 _ = 0
  DistributedStages n d i =
    If (n <=? d)
    {- Then -}
       1
    {- Else -}
       ( If (  -- we don't place a register before the first element
               1 <=? i
            && If -- distribute the hangover blocks to the first r chains
                  (i <=? (n `Mod` (d + 1)) * (n `Div` (d + 1) + 1))
               {- Then -}
                  (i `Mod` (n `Div` (d + 1) + 1) == 0)
               {- Else -}
                  ( (i - n `Mod` (d + 1) * (n `Div` (d + 1) + 1))
                      `Mod` (n `Div` (d + 1))
                    == 0
                  )
            )
         {- Then -}
            1
         {- Else -}
            0
       )

instance
  (KnownNat n, KnownNat m, KnownNat i) ⇒
  KnownNat3 $(nameToSymbol ''DistributedStages) n m i
 where
  natSing3 =
    let
      n = GHC.natVal (Proxy @n)
      m = GHC.natVal (Proxy @m)
      i = GHC.natVal (Proxy @i)
      r = f n m i
    in
      SNatKn r
   where
    f ∷ Nat → Nat → Nat → Nat
    f n m i
      | n == 0 = 0
      | n <= m = 1
      | otherwise =
          let k = n `div` (m + 1)
              r = n `mod` (m + 1)
              b = (k + 1) * r
           in if 1 <= i &&
                   if i <= b
                   then i `mod` (k + 1) == 0
                   else (i - b) `mod` k == 0
              then 1
              else 0
  {-# INLINE natSing3 #-}

-- | Evidence that we never distribute more than one register per
-- stage. The property trivially holds, as the first conditional only
-- selects between the constants zero and one.
--
-- prop> ∀ x y z ∈ ℕ. DistributedStages x y z ≤ 1
atMostOnePerStage ∷ ∀ x y z. Dict (DistributedStages x y z ≤ 1)
atMostOnePerStage = unsafeCoerce (Dict ∷ Dict (0 ≤ 0))

-- | Evenly distributes @d@ registers between @n@ combinational
-- computations. The computations all share a common input given via
-- the first argument and are chained via their second arguemnt. The
-- introduced registers are all initialized with the provided initial
-- value. The introduced delay is tracked using 'DSignal'.
--
-- __Illustration:__ for introducing a register after every second computation
--
-- @
--   shared input  ──┬────┬────────┬────┬──────────────┐
--                   ↓    ↓        ↓    ↓              ↓
--    front input  → c₀ → c₁ → R → c₂ → c₃ → R → ... → cₙ →  output
--                             ⇡             ⇡
--                             vᵢ            vᵢ
-- @
distributeStages ∷
  ∀ (d ∷ Nat) (n ∷ Nat) (a ∷ Type) (b ∷ Type).
  (KnownNat n, NFDataX a) ⇒
  SNat d →
  -- ^ number of stages
  a →
  -- ^ initial value (vᵢ) assigned to the introduced registers after
  -- coming out of the reset
  Vec n (b → a → a) →
  -- ^ the computations to be added in between the different stages.
  ∀ (dom ∷ Domain) (k ∷ Nat).
  (KnownDomain dom, HiddenClockResetEnable dom) ⇒
  DSignal dom k b →
  -- ^ the /shared input/ that is shared among all computations
  DSignal dom k a →
  -- ^ the /front input/ that is fed at the beginning of the chain
  DSignal dom (k + d) a
  -- ^ the output coming out of the chain
distributeStages d@SNat ival computations =
  distributeStages# (SNat @0) d (reverse computations)
 where
  distributeStages# ∷
    ∀ (m ∷ Nat) (i ∷ Nat) (r ∷ Nat).
    (KnownNat m, NFDataX a) ⇒
    SNat i → SNat r →
    Vec m (b → a → a) →
    ∀ (dom ∷ Domain) (k ∷ Nat).
    (KnownDomain dom, HiddenClockResetEnable dom) ⇒
    DSignal dom k b →
    DSignal dom k a →
    DSignal dom (k + r) a
  distributeStages# i@SNat r@SNat cs s = case toUNat @m SNat of
    UZero   → delayedI ival
    USucc _ → case toUNat r of
      UZero
        → liftA2 (head cs) s
        . distributeStages# (succSNat i) r (tail cs) s
      USucc _
        | Dict ← atMostOnePerStage @n @d @i
        , Dict ← leTrans @(DistributedStages n d i) @1 @(r - 1 + 1)
        → delayedI @(DistributedStages n d i) ival
        . liftA2 (head cs) (forward SNat s)
        . distributeStages#
            (succSNat i)
            (SNat @(r - DistributedStages n d i))
            (tail cs)
            s

--------------
-- Internal --
--------------

{-
-- | Some quick test code for checking the 'DistributedStages' type
-- family calculation
_placeRegister ∷ Nat → Nat → IO ()
_placeRegister n m = do
  print (k, r, b)
  putStrLn "---"
  forM_ chain $ \(i, c) → do
    when c $ putStrLn "[R]"
    putStr " "
    print i
 where
  -- minimum size of chained blocks without a register in between
  k = n `div` (m + 1)
  -- number of hangover blocks
  r = n `mod` (m + 1)
  -- add-one-more range bound
  b = (k + 1) * r

  chain
    | m <= 0    = ( , False) <$> [0..n-1]
    | m >= n    = (0, False) : (( , True) <$> [1..n-1])
    | otherwise =
        [ (i, i > 0 && cond)
        | i <- [0..n-1]
        , let cond = if i <= b
                     then i `mod` (k + 1) == 0
                     else (i - b) `mod` k == 0
        ]
-}
