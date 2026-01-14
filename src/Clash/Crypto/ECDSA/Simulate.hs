-- | Types and a simplification procedure to facilitate symbolic execution of
-- the ECDSA signing algorithm. 'EcdsaSymbol' contains constructors that
-- represent intermediate values in the calculation of point addition, scalar
-- multiplication and signing. 'simp' detects the structure of the intermediate
-- values and translates them to instances of 'EcdsaSymbol'.
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# LANGUAGE PatternSynonyms #-}
module Clash.Crypto.ECDSA.Simulate where

import Prelude
import Clash.Crypto.Calculator.Simulate (SymbolicNum, FixChoice(..))
import qualified Clash.Crypto.Calculator.Simulate as Sim
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import GHC.TypeNats (Nat)

-- | Choice fixpoint of 'SymbolicNum' and 'EcdsaSymbol'.
type Sym = FixChoice (SymbolicNum Nat) EcdsaSymbol

var ∷ String → Sym
var = FixRight . Var_

vars ∷ String → [Sym]
vars = fmap var . words

data Point2 r = Point2 { x₁ ∷ r, y₁ ∷ r, x₂ ∷ r, y₂ ∷ r } deriving (Eq, Show, Functor, Generic, NFData)

data MulStep r = MulStep { step ∷ r, x ∷ r, y ∷ r } deriving (Eq, Show, Functor, Generic, NFData)

data EcdsaSymbol r
  = Var_ String
  | Not_ r
  | IsZero_ r
  | IsInfinite_ r r
  | Equals_ r r
  | PointEquals_ (Point2 r)
  | SlopeDiv_ (Point2 r)
  | Square_ r
  | SlopeNum_ (Point2 r)
  | Slope_ (Point2 r)
  | Valid_ (Point2 r)
  | ValidAddX_ (Point2 r)
  | ValidAddY_ (Point2 r)
  | AddX_ (Point2 r)
  | AddY_ (Point2 r)
  | MulStepPointX_ (MulStep r)
  | MulStepPointY_ (MulStep r)
  | MulStepAccX_ r (MulStep r)
  | MulStepAccY_ r (MulStep r)
  | MulX_ r r r
  | MulY_ r r r
  | Hash_
  | Nonce_
  | PrivKey_
  | GX_
  | GY_
  | R_
  | S_
  deriving (Eq, Show, Functor, Generic, NFData)

pattern Lit l = FixLeft (Sim.Lit l)
pattern Add x y = FixLeft (Sim.Add x y)
pattern Sub x y = FixLeft (Sim.Sub x y)
pattern Mul x y = FixLeft (Sim.Mul x y)
pattern Inv x z = FixLeft (Sim.Inv x z)
pattern Bit x b = FixLeft (Sim.Bit x b)
pattern Var s = FixRight (Var_ s)
pattern Not x = FixRight (Not_ x)
pattern IsZero x = FixRight (IsZero_ x)
pattern IsInfinite x y = FixRight (IsInfinite_ x y)
pattern Equals x y = FixRight (Equals_ x y)
pattern PointEquals p = FixRight (PointEquals_ p)
pattern SlopeDiv p = FixRight (SlopeDiv_ p)
pattern SlopeNum p = FixRight (SlopeNum_ p)
pattern Slope p = FixRight (Slope_ p)
pattern Square x = FixRight (Square_ x)
pattern Valid x = FixRight (Valid_ x)
pattern ValidAddX x = FixRight (ValidAddX_ x)
pattern ValidAddY x = FixRight (ValidAddY_ x)
pattern AddX x = FixRight (AddX_ x)
pattern AddY x = FixRight (AddY_ x)
pattern MulX s x y = FixRight (MulX_ s x y)
pattern MulY s x y = FixRight (MulY_ s x y)
pattern MulStepPointX p = FixRight (MulStepPointX_ p)
pattern MulStepPointY p = FixRight (MulStepPointY_ p)
pattern MulStepAccX s p = FixRight (MulStepAccX_ s p)
pattern MulStepAccY s p = FixRight (MulStepAccY_ s p)
pattern Hash = FixRight Hash_
pattern Nonce = FixRight Nonce_
pattern PrivKey = FixRight PrivKey_
pattern GX = FixRight GX_
pattern GY = FixRight GY_
pattern R = FixRight R_
pattern S = FixRight S_

-- | Detect structures that represent an intermediate value in the computation
-- of point addition, scalar multiplication and ecdsa signing, and compress them
-- into an 'EcdsaSymbol'.
simp ∷ Sym → Sym
simp (Lit x `Add` Lit y) = Lit (x + y)
simp (1 `Sub` x) = Not x
simp (Bit (x₁ `Sub` 1) 255 `Mul` (Not (Bit x₂ 255)))
  | x₁ == x₂ = IsZero x₁
simp (IsZero (x `Sub` y)) = Equals x y
simp (Equals y₂ y₁ `Mul` Equals x₂ x₁) =
  PointEquals (Point2 { x₁, y₁, x₂, y₂ })
simp (IsZero y `Mul` IsZero x) = IsInfinite x y
simp (Square (IsZero x)) = IsInfinite x x
simp ((Not (PointEquals p) `Mul` (x₁ `Sub` x₂)) `Add` ((y₁ `Add` y₁') `Mul` PointEquals p'))
  | p == p'
  , p.x₁ == x₁
  , p.x₂ == x₂
  , p.y₁ == y₁
  , p.y₁ == y₁'
  = SlopeDiv p
simp (x `Mul` x') | x == x' = Square x
simp
  (((y₁ `Sub` y₂) `Mul` Not (PointEquals p))
    `Add`
  (((Square x₁ `Add` (Square x₁' `Add` Square x₁'')) `Add` _a) `Mul` PointEquals p'))
  | p == p'
  , p.y₁ == y₁
  , p.y₂ == y₂
  , p.x₁ == x₁
  , p.x₁ == x₁'
  , p.x₁ == x₁''
  -- we just hope a is correct I guess
  = SlopeNum p
simp (SlopeNum p `Mul` Inv (SlopeDiv p') 0) | p == p' = Slope p
simp (Not (IsZero (SlopeDiv p)) `Mul` (Not (IsInfinite x₂ y₂) `Mul` Not (IsInfinite x₁ y₁)))
  | p == Point2 x₁ y₁ x₂ y₂
  = Valid p
simp (Not (IsZero (SlopeDiv p)) `Mul` Square (Not (IsInfinite x₁ y₁)))
  | p == Point2 x₁ y₁ x₁ y₁
  = Valid p
simp ((Square (Slope p) `Sub` x₁ `Sub` x₂) `Mul` (Valid p'))
  | p == p'
  , p.x₁ == x₁
  , p.x₂ == x₂
  = ValidAddX p
simp ((((x₁ `Sub` AddX p) `Mul` Slope p') `Sub` y₁) `Mul` Valid p'')
  | p == p'
  , p == p''
  , p.x₁ == x₁
  , p.y₁ == y₁
  = ValidAddY p
simp ((((MulStepPointX r@MulStep { step = Lit step } `Sub` x) `Mul` Slope p) `Sub` y₁) `Mul` Valid p')
  | x == MulStepPointX (r { step = Lit (step + 1) })
  , p ==
      let px = MulStepPointX r
          py = MulStepPointY r
       in Point2 px py px py
  , p == p'
  , p.y₁ == y₁
  = ValidAddY p
simp (((((Bit s b `Mul` MulStepPointX r@MulStep { step = Lit step }) `Sub` x) `Mul` Slope p) `Sub` y₁) `Mul` Valid p')
  | x == MulStepAccX s (r { step = Lit (step + 1) })
  , b == r.step
  , p == Point2
    { x₁ = Bit s b `Mul` MulStepPointX r
    , y₁ = Bit s b `Mul` MulStepPointY r
    , x₂ = (if r.step == 0 then 0 else MulStepAccX s r)
    , y₂ = (if r.step == 0 then 0 else MulStepAccY s r)
    }
  , p == p'
  , p.y₁ == y₁
  = ValidAddY p
simp (((((Bit Nonce 0 `Mul` gx) `Sub` MulStepAccX Nonce (MulStep 1 gx' gy')) `Mul` Slope p) `Sub` (Bit Nonce 0 `Mul` gy)) `Mul` Valid p')
  | gx == gx' && gy == gy'
  , p == Point2 (Bit Nonce 0 `Mul` gx) (Bit Nonce 0 `Mul` gy) 0 0
  , p == p'
  = ValidAddY p

simp ((((GX `Sub` MulStepPointX r) `Mul` Slope p) `Sub` GY) `Mul` Valid p')
  | r == MulStep 1 GX GY
  , p == Point2 GX GY GX GY
  , p == p'
  = ValidAddY p

simp (ValidAddX p `Add` (x₁' `Mul` IsInfinite x₂ y₂) `Add` (x₂' `Mul` IsInfinite x₁ y₁))
  | p == Point2 x₁ y₁ x₂ y₂
  , x₁ == x₁'
  , x₂ == x₂'
  = AddX p
simp (ValidAddY p `Add` (y₁' `Mul` IsInfinite x₂ y₂) `Add` (y₂' `Mul` IsInfinite x₁ y₁))
  | p == Point2 x₁ y₁ x₂ y₂
  , y₁ == y₁'
  , y₂ == y₂'
  = AddY p

simp (AddX (Point2 (MulStepPointX p) (MulStepPointY p') (MulStepPointX p'') (MulStepPointY p''')))
  | p == p'
  , p == p''
  , p == p'''
  = MulStepPointX (MulStep (p.step + 1) p.x p.y)
simp (AddY (Point2 (MulStepPointX p) (MulStepPointY p') (MulStepPointX p'') (MulStepPointY p''')))
  | p == p'
  , p == p''
  , p == p'''
  = MulStepPointY (MulStep (p.step + 1) p.x p.y)
simp
  (AddX (Point2
    (Bit s b `Mul` MulStepPointX p) (Bit s' b' `Mul` MulStepPointY p')
    (MulStepAccX s'' p'') (MulStepAccY s''' p''')
  ))
  | p == p' && p == p'' && p == p'''
  , s == s' && s == s'' && s == s'''
  , b == b' && b == p.step
  = MulStepAccX s (p { step = p.step `Add` 1})
simp
  (AddY (Point2
    (Bit s b `Mul` MulStepPointX p) (Bit s' b' `Mul` MulStepPointY p')
    (MulStepAccX s'' p'') (MulStepAccY s''' p''')
  ))
  | p == p' && p == p'' && p == p'''
  , s == s' && s == s'' && s == s'''
  , b == b' && b == p.step
  = MulStepAccY s (p { step = p.step `Add` 1})
simp (MulStepAccX s (MulStep 256 x y)) = MulX s x y
simp (MulStepAccY s (MulStep 256 x y)) = MulY s x y
simp
  (AddX (Point2
    (Bit s 0 `Mul` MulStepPointX p) (Bit s' 0 `Mul` MulStepPointY p')
    0 0
  ))
  | p == p' && s == s' && p.step == 0
  = MulStepAccX s (p { step = 1})
simp
  (AddY (Point2
    (Bit s 0 `Mul` MulStepPointX p) (Bit s' 0 `Mul` MulStepPointY p')
    0 0
  ))
  | p == p' && s == s' && p.step == 0
  = MulStepAccY s (p { step = 1})

simp (AddX (Point2 (Bit Nonce 0 `Mul` gx) (Bit Nonce 0 `Mul` gy) 0 0))
  = MulStepAccX Nonce (MulStep 1 gx gy)
simp (AddY (Point2 (Bit Nonce 0 `Mul` gx) (Bit Nonce 0 `Mul` gy) 0 0))
  = MulStepAccY Nonce (MulStep 1 gx gy)

simp (Lit 0x6b17d1f2_e12c4247_f8bce6e5_63a440f2_77037d81_2deb33a0_f4a13945_d898c296)
  = GX
simp (Lit 0x4fe342e2_fe1a7f9b_8ee7eb4a_7c0f9e16_2bce3357_6b315ece_cbb64068_37bf51f5)
  = GY

simp (AddX (Point2 GX GY GX GY))
  = MulStepPointX (MulStep 1 GX GY)
simp (AddY (Point2 GX GY GX GY))
  = MulStepPointY (MulStep 1 GX GY)

simp ((MulX Nonce GX GY) `Add` 0) = R
simp (((PrivKey `Mul` R) `Add` Hash) `Mul` (Inv Nonce 0)) = S

simp x = x
