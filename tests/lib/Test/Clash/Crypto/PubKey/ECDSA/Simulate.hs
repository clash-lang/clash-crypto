{-|
Module      : Test.Clash.Crypto.PubKey.ECDSA.Simulate
Copyright   : Copyright © 2025-2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Types and a simplification procedure to facilitate symbolic execution of
the ECDSA signing algorithm:

* 'EcdsaSymbol' contains constructors that represent intermediate values
  in the calculation of point addition, scalar multiplication and signing.
* 'simp' detects the structure of the intermediate values and translates
  them to instances of 'EcdsaSymbol'.
-}

{-# LANGUAGE PatternSynonyms #-}

module Test.Clash.Crypto.PubKey.ECDSA.Simulate where

import Prelude
import Test.Clash.Crypto.Calculator.Simulate (SymbolicNum, FixChoice(..))
import qualified Test.Clash.Crypto.Calculator.Simulate as Sim
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import GHC.TypeNats (Nat)

-- * ECDSA Symbols

-- | The parameters of a symbolic binary point operation.
data Point2 r = Point2
  { x₁ ∷ r
  , y₁ ∷ r
  , x₂ ∷ r
  , y₂ ∷ r
  }
  deriving (Eq, Show, Functor, Generic, NFData)

-- | The parameters of a symbolic multiplication step.
data MulStep r = MulStep
  { step ∷ r
  , x ∷ r
  , y ∷ r
  }
  deriving (Eq, Show, Functor, Generic, NFData)

-- | Symbols for different structures of ECDSA.
data EcdsaSymbol r
  = -- | variables
    Var_ String
  | -- | negation
    Not_ r
  | -- | zero check
    IsZero_ r
  | -- | infinity check
    IsInfinite_ r r
  | -- | equality
    Equals_ r r
  | -- | point equality
    PointEquals_ (Point2 r)
  | -- | slope div calculation
    SlopeDiv_ (Point2 r)
  | -- | square calculation
    Square_ r
  | -- | slope num calculation
    SlopeNum_ (Point2 r)
  | -- | slope calculation
    Slope_ (Point2 r)
  | -- | point validation
    Valid_ (Point2 r)
  | -- | validated point x addition
    ValidAddX_ (Point2 r)
  | -- | validated point y addition
    ValidAddY_ (Point2 r)
  | -- | point x addition
    AddX_ (Point2 r)
  | -- | point y addition
    AddY_ (Point2 r)
  | -- | point x multiplication step
    MulStepPointX_ (MulStep r)
  | -- | point y multiplication step
    MulStepPointY_ (MulStep r)
  | -- | point x multiplication step with accumulator
    MulStepAccX_ r (MulStep r)
  | -- | point x multiplication step with accumulator
    MulStepAccY_ r (MulStep r)
  | -- | point x multiplication
    MulX_ r r r
  | -- | point y multiplication
    MulY_ r r r
  | -- | hash calculation
    Hash_
  | -- | nonce calculation
    Nonce_
  | -- | private key generation
    PrivKey_
  | -- | x-coordinate of the curveBasePoint field
    GX_
  | -- | y-coordinate of the curveBasePoint field
    GY_
  | -- | some intermediate result
    R_
  | -- | some intermediate result
    S_
  deriving (Eq, Show, Functor, Generic, NFData)

-- | Symbolic numeric literals.
pattern Lit ∷ l → FixChoice (SymbolicNum l) r
pattern Lit l = FixLeft (Sim.Lit l)

pattern Add, Sub, Mul, Inv, Bit ∷
  FixChoice (SymbolicNum l) r →
  FixChoice (SymbolicNum l) r →
  FixChoice (SymbolicNum l) r

-- | Symbolic addition.
pattern Add x y = FixLeft (Sim.Add x y)
-- | Symbolic substraction.
pattern Sub x y = FixLeft (Sim.Sub x y)
-- | Symbolic multiplication.
pattern Mul x y = FixLeft (Sim.Mul x y)
-- | Symbolic modulo inverse.
pattern Inv x z = FixLeft (Sim.Inv x z)
-- | Symbolic bit check.
pattern Bit x b = FixLeft (Sim.Bit x b)

-- | Symbolic variables.
pattern Var ∷ String → FixChoice l EcdsaSymbol
pattern Var s = FixRight (Var_ s)

pattern Not, IsZero, Square ∷
  FixChoice l EcdsaSymbol →
  FixChoice l EcdsaSymbol

-- | Symbolic negation.
pattern Not x = FixRight (Not_ x)
-- | Symbolic zero check.
pattern IsZero x = FixRight (IsZero_ x)
-- | Symbolic square calculation.
pattern Square x = FixRight (Square_ x)

pattern IsInfinite, Equals ∷
  FixChoice l EcdsaSymbol →
  FixChoice l EcdsaSymbol →
  FixChoice l EcdsaSymbol

-- | Symbolic infinity check.
pattern IsInfinite x y = FixRight (IsInfinite_ x y)
-- | Symbolic equality check.
pattern Equals x y = FixRight (Equals_ x y)

pattern PointEquals, SlopeDiv, SlopeNum, Slope,
        Valid, ValidAddX, ValidAddY, AddX, AddY ∷
  Point2 (FixChoice l EcdsaSymbol) →
  FixChoice l EcdsaSymbol

-- | Symbolic point equality check.
pattern PointEquals p = FixRight (PointEquals_ p)
-- | Symbolic slope div calculation.
pattern SlopeDiv p = FixRight (SlopeDiv_ p)
-- | Symbolic slope num calculation.
pattern SlopeNum p = FixRight (SlopeNum_ p)
-- | Symbolic slope calculation.
pattern Slope p = FixRight (Slope_ p)
-- | Symbolically validated point.
pattern Valid x = FixRight (Valid_ x)
-- | Symbolically validated point x addition.
pattern ValidAddX x = FixRight (ValidAddX_ x)
-- | Symbolically validated point y addition.
pattern ValidAddY x = FixRight (ValidAddY_ x)
-- | Symbolic point x addition.
pattern AddX x = FixRight (AddX_ x)
-- | Symbolic point y addition.
pattern AddY x = FixRight (AddY_ x)

pattern MulX, MulY ∷
  FixChoice l EcdsaSymbol →
  FixChoice l EcdsaSymbol →
  FixChoice l EcdsaSymbol →
  FixChoice l EcdsaSymbol

-- | Symbolic point x multiplication.
pattern MulX s x y = FixRight (MulX_ s x y)
-- | Symbolic point y multiplication.
pattern MulY s x y = FixRight (MulY_ s x y)

pattern MulStepPointX, MulStepPointY ∷
  MulStep (FixChoice l EcdsaSymbol) →
  FixChoice l EcdsaSymbol

-- | Symbolic point x multiplication step.
pattern MulStepPointX p = FixRight (MulStepPointX_ p)
-- | Symbolic point y multiplication step.
pattern MulStepPointY p = FixRight (MulStepPointY_ p)

pattern MulStepAccX, MulStepAccY ∷
  FixChoice l EcdsaSymbol →
  MulStep (FixChoice l EcdsaSymbol) →
  FixChoice l EcdsaSymbol

-- | Symbolic point x multiplication step with accumulator.
pattern MulStepAccX s p = FixRight (MulStepAccX_ s p)
-- | Symbolic point y multiplication step with accumulator.
pattern MulStepAccY s p = FixRight (MulStepAccY_ s p)

pattern Hash, Nonce, PrivKey, GX, GY, R, S ∷
  FixChoice l EcdsaSymbol

-- | Symbolic hash calculation.
pattern Hash = FixRight Hash_
-- | Symbolic nonce calculation.
pattern Nonce = FixRight Nonce_
-- | Symbolic private key generation.
pattern PrivKey = FixRight PrivKey_
-- | Symbolic x-coordinate of the curve's base point field.
pattern GX = FixRight GX_
-- | Symbolic x-coordinate of the curve's base point field.
pattern GY = FixRight GY_
-- | Symbolic intermediate result.
pattern R = FixRight R_
-- | Symbolic intermediate result.
pattern S = FixRight S_

-- * Symbolic Simplification

-- | Detect structures that represent an intermediate value in the computation
-- of point addition, scalar multiplication and ECDSA signing, and compress them
-- into an 'EcdsaSymbol'.
simp ∷ Sym → Sym

simp (Lit x `Add` Lit y)
  = Lit (x + y)

simp (1 `Sub` x)
  = Not x

simp (Bit (x₁ `Sub` 1) 255 `Mul` (Not (Bit x₂ 255)))
  | x₁ == x₂
  = IsZero x₁

simp (IsZero (x `Sub` y))
  = Equals x y

simp (Equals y₂ y₁ `Mul` Equals x₂ x₁)
  = PointEquals (Point2 { x₁, y₁, x₂, y₂ })

simp (IsZero y `Mul` IsZero x)
  = IsInfinite x y

simp (Square (IsZero x))
  = IsInfinite x x

simp (x `Add` y)
  | Not (PointEquals p₀) `Mul` (x₁ `Sub` x₂) ← x
  , (y₁ `Add` y₂) `Mul` PointEquals p₁ ← y
  , p₀ == p₁
  , p₀.x₁ == x₁
  , p₀.x₂ == x₂
  , p₀.y₁ == y₁
  , p₀.y₁ == y₂
  = SlopeDiv p₀

simp (x₀ `Mul` x₁)
  | x₀ == x₁
  = Square x₀

simp (y `Add` x)
  | (y₁ `Sub` y₂) `Mul` Not (PointEquals p₀) ← y
  , z `Mul` PointEquals p₁ ← x
  , (Square x₁ `Add` (Square x₂ `Add` Square x₃)) `Add` _ ← z
  , p₀ == p₁
  , p₀.y₁ == y₁
  , p₀.y₂ == y₂
  , p₀.x₁ == x₁
  , p₀.x₁ == x₂
  , p₀.x₁ == x₃
  -- we just hope a is correct I guess
  = SlopeNum p₀

simp (SlopeNum p₀ `Mul` Inv (SlopeDiv p₁) 0)
  | p₀ == p₁
  = Slope p₀

simp (Not (IsZero (SlopeDiv p)) `Mul` (e₀ `Mul` e₁))
  | Not (IsInfinite x₂ y₂) ← e₀
  , Not (IsInfinite x₁ y₁) ← e₁
  , p == Point2 x₁ y₁ x₂ y₂
  = Valid p

simp (e₀ `Mul` e₁)
  | Not (IsZero (SlopeDiv p)) ← e₀
  , Square (Not (IsInfinite x₁ y₁)) ← e₁
  , p == Point2 x₁ y₁ x₁ y₁
  = Valid p

simp ((Square (Slope p₀) `Sub` x₁ `Sub` x₂) `Mul` (Valid p₁))
  | p₀ == p₁
  , p₀.x₁ == x₁
  , p₀.x₂ == x₂
  = ValidAddX p₀

simp ((((x₁ `Sub` AddX p₀) `Mul` Slope p₁) `Sub` y₁) `Mul` Valid p₂)
  | p₀ == p₁
  , p₀ == p₂
  , p₀.x₁ == x₁
  , p₀.y₁ == y₁
  = ValidAddY p₀

simp ((((m `Sub` x) `Mul` Slope p₀) `Sub` y₁) `Mul` Valid p₁)
  | MulStepPointX r@MulStep { step = Lit step } ← m
  , x == MulStepPointX (r { step = Lit (step + 1) })
  , let px = MulStepPointX r
        py = MulStepPointY r
  , p₀ == Point2 px py px py
  , p₀ == p₁
  , p₀.y₁ == y₁
  = ValidAddY p₀

simp (((((Bit s b `Mul` m) `Sub` x) `Mul` Slope p₀) `Sub` y₁) `Mul` Valid p₁)
  | MulStepPointX r@MulStep { step = Lit step } ← m
  , x == MulStepAccX s (r { step = Lit (step + 1) })
  , b == r.step
  , p₀ == Point2 { x₁ = Bit s b `Mul` MulStepPointX r
                 , y₁ = Bit s b `Mul` MulStepPointY r
                 , x₂ = if r.step == 0 then 0 else MulStepAccX s r
                 , y₂ = if r.step == 0 then 0 else MulStepAccY s r
                 }
  , p₀ == p₁
  , p₀.y₁ == y₁
  = ValidAddY p₀

simp (((n `Mul` Slope p₀) `Sub` (Bit Nonce 0 `Mul` gy₀)) `Mul` Valid p₁)
  | (Bit Nonce 0 `Mul` gx₀) `Sub` m ← n
  , MulStepAccX Nonce (MulStep 1 gx₁ gy₁) ← m
  , gx₀ == gx₁ && gy₀ == gy₁
  , p₀ == Point2 (Bit Nonce 0 `Mul` gx₀) (Bit Nonce 0 `Mul` gy₀) 0 0
  , p₀ == p₁
  = ValidAddY p₀

simp ((e `Sub` GY) `Mul` Valid p₀)
  | (GX `Sub` MulStepPointX r) `Mul` Slope p₁ ← e
  , MulStep 1 GX GY ← r
  , Point2 GX GY GX GY ← p₀
  , Point2 GX GY GX GY ← p₁
  = ValidAddY p₀

simp (ValidAddX p `Add` e₀ `Add` e₁)
  | x₃ `Mul` IsInfinite x₂ y₂ ← e₀
  , x₄ `Mul` IsInfinite x₁ y₁ ← e₁
  , p == Point2 x₁ y₁ x₂ y₂
  , x₁ == x₃
  , x₂ == x₄
  = AddX p

simp (ValidAddY p `Add` e₀ `Add` e₁)
  | y₃ `Mul` IsInfinite x₂ y₂ ← e₀
  , y₄ `Mul` IsInfinite x₁ y₁ ← e₁
  , p == Point2 x₁ y₁ x₂ y₂
  , y₁ == y₃
  , y₂ == y₄
  = AddY p

simp (AddX (Point2 x₀ y₀ x₁ y₁))
  | MulStepPointX p₀ ← x₀
  , MulStepPointY p₁ ← y₀
  , MulStepPointX p₂ ← x₁
  , MulStepPointY p₃ ← y₁
  , p₀ == p₁
  , p₀ == p₂
  , p₀ == p₃
  = MulStepPointX (MulStep (p₀.step + 1) p₀.x p₀.y)

simp (AddY (Point2 x₀ y₀ x₁ y₁))
  | MulStepPointX p₀ ← x₀
  , MulStepPointY p₁ ← y₀
  , MulStepPointX p₂ ← x₁
  , MulStepPointY p₃ ← y₁
  , p₀ == p₁
  , p₀ == p₂
  , p₀ == p₃
  = MulStepPointY (MulStep (p₀.step + 1) p₀.x p₀.y)

simp (AddX (Point2 x₀ y₀ x₁ y₁))
  | Bit s₀ b₀ `Mul` MulStepPointX p₀ ← x₀
  , Bit s₁ b₁ `Mul` MulStepPointY p₁ ← y₀
  , MulStepAccX s₂ p₂ ← x₁
  , MulStepAccY s₃ p₃ ← y₁
  , p₀ == p₁ && p₀ == p₂ && p₀ == p₃
  , s₀ == s₁ && s₀ == s₂ && s₀ == s₃
  , b₀ == b₁ && b₀ == p₀.step
  = MulStepAccX s₀ (p₀ { step = p₀.step `Add` 1})

simp (AddY (Point2 x₀ y₀ x₁ y₁))
  | Bit s₀ b₀ `Mul` MulStepPointX p₀ ← x₀
  , Bit s₁ b₁ `Mul` MulStepPointY p₁ ← y₀
  , MulStepAccX s₂ p₂ ← x₁
  , MulStepAccY s₃ p₃ ← y₁
  , p₀ == p₁ && p₀ == p₂ && p₀ == p₃
  , s₀ == s₁ && s₀ == s₂ && s₀ == s₃
  , b₀ == b₁ && b₀ == p₀.step
  = MulStepAccY s₀ (p₀ { step = p₀.step `Add` 1})

simp (MulStepAccX s (MulStep 256 x y)) = MulX s x y

simp (MulStepAccY s (MulStep 256 x y)) = MulY s x y

simp (AddX (Point2 x y 0 0))
  | Bit s₀ 0 `Mul` MulStepPointX p₀ ← x
  , Bit s₁ 0 `Mul` MulStepPointY p₁ ← y
  , p₀ == p₁
  , s₀ == s₁
  , p₀.step == 0
  = MulStepAccX s₀ (p₀ { step = 1})

simp (AddY (Point2 x y 0 0))
  | Bit s₀ 0 `Mul` MulStepPointX p₀ ← x
  , Bit s₁ 0 `Mul` MulStepPointY p₁ ← y
  , p₀ == p₁
  , s₀ == s₁
  , p₀.step == 0
  = MulStepAccY s₀ (p₀ { step = 1})

simp (AddX (Point2 (Bit Nonce 0 `Mul` gx) (Bit Nonce 0 `Mul` gy) 0 0))
  = MulStepAccX Nonce (MulStep 1 gx gy)

simp (AddY (Point2 (Bit Nonce 0 `Mul` gx) (Bit Nonce 0 `Mul` gy) 0 0))
  = MulStepAccY Nonce (MulStep 1 gx gy)

simp (Lit x) = case x of
  0x6b17d1f2_e12c4247_f8bce6e5_63a440f2_77037d81_2deb33a0_f4a13945_d898c296 → GX
  0x4fe342e2_fe1a7f9b_8ee7eb4a_7c0f9e16_2bce3357_6b315ece_cbb64068_37bf51f5 → GY
  _ → Lit x

simp (AddX (Point2 GX GY GX GY))
  = MulStepPointX (MulStep 1 GX GY)

simp (AddY (Point2 GX GY GX GY))
  = MulStepPointY (MulStep 1 GX GY)

simp ((MulX Nonce GX GY) `Add` 0) = R

simp (((PrivKey `Mul` R) `Add` Hash) `Mul` (Inv Nonce 0)) = S

simp x = x

-- * Utility Functions

-- | Choice fixpoint of 'SymbolicNum' and 'EcdsaSymbol'.
type Sym = FixChoice (SymbolicNum Nat) EcdsaSymbol

-- | Symbolic variable constructor.
var ∷ String → Sym
var = FixRight . Var_

-- | Constructs multiple symbolic variables at once using a space
-- separated string of variable names.
vars ∷ String → [Sym]
vars = fmap var . words