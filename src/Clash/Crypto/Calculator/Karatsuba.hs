{-|
Module      : Clash.Crypto.Calculator.Karatsuba
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Implementation of big-number multiplication using Karatsuba's algorithm.
-}

{-# LANGUAGE TypeAbstractions #-}

module Clash.Crypto.Calculator.Karatsuba
  ( KaratsubaCycles
  , karatsuba
  , karatsubaSequential
  , karatsubaSequentialModulo
  ) where

import Clash.Prelude.Safe

import Clash.Signal.Channel
import Clash.Signal.Extra (apWhen)

import Data.Constraint.Nat.Extra
  ( Div2RoundsDown, HalfIsLess, HalfIsLessInverse, HalfLowerBound
  )
import GHC.TypeNats.Proof (Rewrite(..), using)

import Clash.Crypto.Calculator.Modulo (computeUnsignedModuloUnsigned)

-- * Combinatorial implementations

-- | The number of bits of the low part.
type Low  n = n `Div` 2

-- | The number of bits of the high part.
type High n = n - n `Div` 2

-- | Combinational Karatsuba implementation that recurses as long as
-- the size of at least one of the operands is larger than the given
-- lower bound @k@. Not meant to be synthesized in the case of large
-- numbers.
karatsuba ∷
  ∀ (n ∷ Nat) (m ∷ Nat). (KnownNat n, KnownNat m) ⇒
  -- | The lower bound defining the base case at which standard
  -- multiplication is used instead of another recursive call
  ∀ regBound → KnownNat regBound ⇒
  Unsigned n → Unsigned m → Unsigned (n + m)
karatsuba regBound x y
  | SNat @s ← SNat @(Max n m)
  , Rewrite ← using @(HalfIsLess s)
  = case ( compareSNat (SNat @(n + m)) (SNat @regBound)
         , compareSNat (SNat @4) (SNat @s)
         ) of
      (SNatGT, SNatLE)
        → resize z₀
        + resize (extendRight @(Low s) z₁)
        + resize (extendRight @(Low s + Low s) z₂)
       where
        xₗₒ, yₗₒ ∷ Unsigned (Low s)
        xₕᵢ, yₕᵢ ∷ Unsigned (High s)
        (xₕᵢ, xₗₒ) = bitCoerce $ resize x
        (yₕᵢ, yₗₒ) = bitCoerce $ resize y

        xₛ, yₛ ∷ Unsigned (High s + 1)
        xₛ = resize xₕᵢ + resize xₗₒ
        yₛ = resize yₕᵢ + resize yₗₒ

        z₀, z₁, z₂ ∷ Unsigned ((High s + 1) + (High s + 1))
        z₀ = resize $ karatsuba regBound xₗₒ yₗₒ
        z₂ = resize $ karatsuba regBound xₕᵢ yₕᵢ
        z₃ = karatsuba regBound xₛ yₛ
        z₁ = z₃ - z₂ - z₀

      _ → extend x * extend y

-- -- * Sequential implementations

-- |The number of cycles an instance of 'karatsubaSequential` takes to run.
type KaratsubaCycles stages = 2 * (3 ^ stages - 1)

-- |A sequential implementation of the Karatsuba algorithm for multiplication.
-- It supports recursion on the size of its arguments, dividing the length
-- by 2 each time it recurs, relying on both sequential and combinatorial
-- subcircuits, which depths are configurable at type-level.  'regSize' gives
-- the size of the multiplication units of the board, that will enable the
-- algorithm to compute the appropriate depth.
-- This algorithm uses two-step semantics with a toggle line that starts on
-- `False`.
--
-- __Example:__
-- @
-- karatsubaSequential @3 @36 @256 @256
-- @
-- will produce a sequential circuit with latency '52 = 2 * (3 ^ cycles - 1)'
-- that is able to multiply two 256-bit unsigned numbers.
karatsubaSequential ∷
  ∀ (n ∷ Nat) (m ∷ Nat) (dom ∷ Domain).
  (KnownNat n, KnownNat m, HiddenClockResetEnable dom) ⇒
  ∀ stages → KnownNat stages ⇒
  ∀ k → KnownNat k ⇒
  Channel dom (Unsigned n, Unsigned m) →
  Channel dom (Unsigned (n + m))
karatsubaSequential stages k input
  | SNat @s ← SNat @(Max n m)
  , Rewrite ← using @(HalfIsLess s)
  , Rewrite ← using @(Div2RoundsDown s)
  = case toUNat (SNat @stages) of
      UZero   → uncurry (karatsuba k) <$> input
      USucc _ → fromVec <$> guardC done cur
       where
        -- Collating these values into a vector on which the algorithm
        -- will iterate.
        cur = keepD @(Vec 3 (BitVector (2 * (High s + 1)))) next

        next
          = join (toVec <$> input)
          $ zipRecent (<<+) cur
          $ fmap pack
          $ karatsubaSequential (type (stages - 1)) k
          $ guardC (not <$> done)
          $ bitCoerce @_ @(Unsigned (High s + 1), Unsigned (High s + 1)) . head
              <$> cur

        done = iteration .== 0
         where
          iteration = register (minBound ∷ Index 4)
            $ apWhen input.hasUpdates (const maxBound)
            $ apWhen next.hasUpdates (satPred SatBound)
              iteration

        -- Separate the two numbers into a high part and a low part and
        -- compute the values that'll be given to downstream
        -- multiplications.
        toVec (a, b) = bitCoerce
          $  extend xₕᵢ
          :> extend yₕᵢ
          :> extend xₗₒ
          :> extend @_ @_ @(High s - Low s + 1) yₗₒ
          :> extend yₕᵢ + extend yₗₒ
          :> extend xₕᵢ + extend xₗₒ
          :> Nil
         where
          xₗₒ, yₗₒ ∷ Unsigned (Low s)
          xₕᵢ, yₕᵢ ∷ Unsigned (High s)
          (xₕᵢ, xₗₒ) = bitCoerce $ resize a
          (yₕᵢ, yₗₒ) = bitCoerce $ resize b

        fromVec (bitCoerce → (z₂, z₀, z₃))
          = resize (z₀ ∷ Unsigned ((High s + 1) * 2))
          + resize (extendRight @(Low s) (computeZ₁ z₃ z₂ z₀))
          + resize (extendRight @(Low s + Low s) z₂)

-- | A variant of 'karatsubaSequential', which takes an additional
-- modulus argument and returns the modulo of the computed
-- multiplication. Both multiplication operands are required to be
-- smaller than the given modulus value. A zero modulus argument
-- represents the modulus @2^n@.
karatsubaSequentialModulo ∷
  ∀ (n ∷ Nat) (dom ∷ Domain).
  (KnownNat n, HiddenClockResetEnable dom) ⇒
  ∀ stages → KnownNat stages ⇒
  ∀ regBound → KnownNat regBound ⇒
  Channel dom ((Unsigned n, Unsigned n), Unsigned n) →
  Channel dom (Unsigned n)
karatsubaSequentialModulo _ _ input
  | UZero ← toUNat (SNat @n)
  = fst . fst <$> input
karatsubaSequentialModulo _ _ input
  | USucc UZero ← toUNat (SNat @n)
  = \case { ((1, 1), 0) → 1; _ → 0 } <$> input
karatsubaSequentialModulo stages regBound (unzipC → (input, k))
  | USucc (USucc _) ← toUNat (SNat @n)
  , Rewrite ← using @(HalfIsLessInverse n)
  , Rewrite ← using @(HalfLowerBound n)
  , SNat @lo ← SNat @(Low n)
  , SNat @hi ← SNat @(High n)
  = case toUNat (SNat @stages) of
      UZero
        → delayC
        $ computeUnsignedModuloUnsigned
        $ zipRecent (flip (,)) k
        $ uncurry (karatsuba regBound) <$> input
      USucc @s _
        → channel $ bundle (toM <$> r1, delay Clear m.outAction)
       where
        mulOut
          = computeUnsignedModuloUnsigned
          $ zipRecent (flip (,)) k
          $ karatsubaSequential @(hi + 1) @(hi + 1) s regBound
          $ channel
          $ bundle (bitCoerce <$> r0, m.mulAction)

        mslOut
          = modShiftL
          $ channel
          $ bundle
             ( bundle (bundle (toM <$> r1, mslIndex), plain k)
             -- TODO: this may be not necessary, if 'enhance' would have
             -- Moore semantics instead of Mealy
             , delay Clear m.mslAction
             )

        mslIndex = register (maxBound ∷ Index (2 * lo))
          $ apWhen input.hasUpdates (const maxBound)
          $ apWhen mslOut.hasUpdates (const (natToNum @(lo - 1)))
            mslIndex

        r0i, r1i, r2i ∷ Signal dom (Unsigned (2 * (hi + 1)))
        (r0i, r1i, r2i) = unbundle $ bitCoerce . initialize <$> plain input
         where
          initialize (x, y) =
               extend xₕᵢ
            :> extend yₕᵢ
            :> extend @_ @_ @(hi - lo + 1) xₗₒ
            :> extend @_ @_ @(hi - lo + 1) yₗₒ
            :> extend yₕᵢ + extend yₗₒ
            :> extend xₕᵢ + extend xₗₒ
            :> Nil @(Unsigned (hi + 1))
           where
            xₗₒ, yₗₒ ∷ Unsigned lo
            xₕᵢ, yₕᵢ ∷ Unsigned hi
            (xₕᵢ, xₗₒ) = bitCoerce x
            (yₕᵢ, yₗₒ) = bitCoerce y

        m = go
          <$> input.getContent
          <*> mulOut.hasUpdates
          <*> mslOut.isNonEmpty
          <*> register 0 m.stage
         where
          go None _ _ _ =
            Actions 0 Clear KeepR0 Keep  KeepR1 Keep  KeepR2

          go (Fresh _) _ _ _ =
            Actions 1 Clear InitR0 Clear InitR1 Clear InitR2

          go (Old _) mulResult shLResult s = case s of
            ----                  xₕᵢ,yₕᵢ          xₗₒ,yₗₒ              xₛ,yₛ
            1              → next KeepR0  Release  KeepR1      Clear    KeepR2
            2  | mulResult → next FromMul Keep     KeepR1      Clear    KeepR2
            ----                  z₂               xₗₒ,yₗₒ              xₛ,yₛ
            3              → next FromR2  Clear    FromR0      Clear    FromR1
            ----                  xₛ,yₛ            z₂                   xₗₒ,yₗₒ
            4              → next KeepR0  Release  KeepR1      Release  KeepR2
            5  | mulResult → next FromMul Keep     Negate      Keep     KeepR2
            ----                  z₀               -z₂                  xₗₒ,yₗₒ
            6              → next FromR2  Clear    PlusR0      Keep     KeepR2
            ----                  xₗₒ,yₗₒ          xₛ*yₛ-z₂             ⊥
            7              → next KeepR0  Release  KeepR1      Keep     KeepR2
            8  | mulResult → next FromMul Keep     Negate      Keep     KeepR2
            ----                  z₀               z₂-xₛ*yₛ             ⊥
            9              → next KeepR0  Clear    PlusR0      Keep     KeepR2
            ----                  z₀               z₂+z₀-xₛ*yₛ          ⊥
            10             → next KeepR0  Clear    Negate      Keep     KeepR2
            ----                  z₀               z₁                   ⊥
            11 | shLResult → next KeepR0  Clear    KeepR1      Release  FromShL
            ----                  z₀               z₁                   z₂ˢ
            12             → next FromR2  Clear    FromR0      Keep     KeepR2
            ----                  z₂ˢ              z₀                   ⊥
            13 | shLResult → next KeepR0  Clear    PlusR0      Keep     FromShL
            ----                  ⊥                z₂ˢ+z₀               z₁ˢ
            14             → next FromR2  Clear    KeepR1      Clear    KeepR2
            ----                  z₁ˢ              z₂ˢ+z₀               ⊥
            15             → done KeepR0  Clear    PlusR0      Clear    KeepR2
            ----                  ⊥                z₂ˢ+z₁ˢ+z₀           ⊥
            _              → wait KeepR0  Keep     KeepR1      Keep     KeepR2
            ----
            -- z₀  = xₗₒ * yₗₒ
            -- z₁  = xₛ  * yₛ  - z₂ - z₀
            -- z₂  = xₕᵢ * yₕᵢ
            -- z₁ˢ = z₁ << Low (BitSize p)
            -- z₂ˢ = z₂ << 2 * Low (BitSize p)
           where
            done = Actions 0       Release
            wait = Actions s       Keep
            next = Actions (s + 1) Clear

        r0, r1, r2 ∷ Signal dom (Unsigned (2 * (hi + 1)))
        r0 = register undefined
           $ u0 <$> m.r0Action <*> r0i <*> r0 <*> r2 <*> plain mulOut

        r1 = register undefined
           $ u1 <$> m.r1Action <*> r1i <*> r1 <*> r0 <*> plain k

        r2 = register undefined
           $ u2 <$> m.r2Action <*> r2i <*> r2 <*> r1 <*> plain mslOut

        u0 act i v n o = case act of
          InitR0  → i  ;  KeepR0 → v  ;  FromR2 → n
          FromMul → toU o

        u1 act i v n d = case act of
          InitR1  → i  ;  KeepR1 → v  ;  FromR0 → n
          PlusR0  → toU $ addMod d (toM v) (toM n)
          Negate  → toU $ d - (toM v)

        u2 act i v n o = case act of
          InitR2  → i  ;  KeepR2 → v  ;  FromR1 → n
          FromShL → toU o

        plain ∷ Channel dom a → Signal dom a
        plain = (\case { Fresh x → x; Old x → x; None → undefined } <$>)
             . getContent

        addMod ∷ Unsigned n → Unsigned n → Unsigned n → Unsigned n
        addMod d a b
          | d - a > b = a + b
          | otherwise = b - (d - a)

        toU ∷ Unsigned n → Unsigned (2 * (hi + 1))
        toU = resize

        toM ∷ Unsigned (2 * (hi + 1)) → Unsigned n
        toM = resize

data R0Action = InitR0 | KeepR0 | FromR2 | FromMul
data R1Action = InitR1 | KeepR1 | FromR0 | Negate  | PlusR0
data R2Action = InitR2 | KeepR2 | FromR1 | FromShL

data Actions = Actions
  { stage     ∷ Index 16
  , outAction ∷ ProviderAction
  , r0Action  ∷ R0Action
  , mulAction ∷ ProviderAction
  , r1Action  ∷ R1Action
  , mslAction ∷ ProviderAction
  , r2Action  ∷ R2Action
  }

-- * Helper functions.

computeZ₁ ∷
  ∀ len. KnownNat len ⇒
  Unsigned len → Unsigned len → Unsigned len → Unsigned len
computeZ₁ z₃ z₂ z₀ = z₃ - z₂ - z₀

extendRight ∷
  ∀ b a. (KnownNat a, KnownNat b) ⇒
  Unsigned a → Unsigned (a + b)
extendRight a = bitCoerce (a, 0 ∷ Unsigned b)

modShiftL ∷
  ∀ (n ∷ Nat) (m ∷ Nat) (dom ∷ Domain).
  (KnownNat n, KnownNat m, HiddenClockResetEnable dom) ⇒
  Channel dom ((Unsigned n, Index m), Unsigned n) →
  Channel dom (Unsigned n)
modShiftL
  | USucc _ ← toUNat (SNat @n)
  , USucc _ ← toUNat (SNat @m)
  = enhance fst (const fst) $ \(_, extend → k) (s, j) →
      ( ( truncateB @Unsigned @n @1
        $ let e = unpack $ pack s ++# 0
           in e - if e < k then 0 else k
        , satPred SatBound j
        )
      , j > minBound
      )

  | otherwise = fmap (fst . fst)
