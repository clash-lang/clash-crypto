{-# LANGUAGE MagicHash #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}

module Clash.Crypto.Calculator.Simulate where

import Prelude hiding ((!!))

import Clash.Class.BitPack (BitPack(..))
import Control.DeepSeq (NFData(..))
import Control.Monad (foldM)
import Data.Functor.Identity (Identity(..))
import Data.List (genericIndex, intercalate)
import GHC.Generics (Generic)

import Clash.Crypto.Calculator.ISA
  ( KnownRoutine(..)
  , SomeRoutine(..)
  , RoutineFacts(..)
  , instructions
  , Instruction(..)
  , RequiredStackSize
  , CluInstruction
  , ECPrime
  )
import qualified Clash.Crypto.Calculator.ISA as Calc

run ∷
  ∀ k a .
  ∀ (r :: k) →
  (KnownRoutine r, CalculatorNum a, Show k) ⇒
  [a] → Maybe [a]
run r as
  | RoutineFacts ← knownRoutine @_ @r @a
  = runInstructions (instructions @(RequiredStackSize r) r r) as

runInstructions ∷
  (Foldable f, Integral n, Integral m, Num k, Enum k, CalculatorNum a, Show r) ⇒
  f (Instruction (SomeRoutine r) n m k ECPrime a) →
  [a] → Maybe [a]
runInstructions is as0 = foldl' step (Just as0) is
 where
  step Nothing _ = Nothing
  step (Just as) i = runInstruction i as

traceM ∷
  ∀ k a m .
  ∀ (r ∷ k) →
  (Monad m, Show k, KnownRoutine r, CalculatorNum a, BitPack a) ⇒
  (String → m ()) →
  (a → a) →
  [a] → m (Maybe [a])
traceM r write simplify as
  | RoutineFacts ← knownRoutine @_ @r @a
  = traceInstructionsM write simplify (instructions @(RequiredStackSize r) r r) as

traceInstructionsM ∷
  ( Monad t, Foldable f
  , Show r
  , Integral n, Integral m, Show n, Show m
  , Num k, Enum k, Show k
  , CalculatorNum a
  ) ⇒
  (String → t ()) →
  (a → a) →
  f (Instruction (SomeRoutine r) n m k ECPrime a) →
  [a] → t (Maybe [a])
traceInstructionsM write simplify is (fmap simplify → as0) = do
  write (showStack $ Just as0)
  foldM step (Just as0) is
 where
  step Nothing i = do
    write $ show i
    write $ showStack @() Nothing
    return Nothing
  step (Just as) i = do
    write $ show i
    as' ← fmap (fmap (fmap simplify))
        $ traceInstructionM (const $ pure ()) simplify i as
    write (showStack as')
    rnf as' `seq` return as'

showStack ∷ Show a ⇒ Maybe [a] → String
showStack Nothing   = "↯ Underflow ↯"
showStack (Just []) = "∅ Empty ∅"
showStack (Just as) = intercalate " " $ map (($ "") . showsPrec 11) as

(!!) ∷ Integral i ⇒ [a] → i → a
(!!) = genericIndex

runInstruction ∷
  (Integral n, Integral m, Num k, Enum k, CalculatorNum a, Show r) ⇒
  Instruction (SomeRoutine r) n m k ECPrime a →
  [a] → Maybe [a]
runInstruction i as = runIdentity $ traceInstructionM (const $ pure ()) id i as

traceInstructionM ∷
  (Monad t, Integral n, Integral m, Num k, Enum k, CalculatorNum a, Show r) ⇒
  (String → t ()) →
  (a → a) →
  Instruction (SomeRoutine r) n m k ECPrime a →
  [a] → t (Maybe [a])
traceInstructionM write simplify = go
 where
  go (PUT a) as
    = pure $ Just $ a:as
  go (POP n) as
    | fromIntegral n <= length as
    = pure $ Just $ drop (fromIntegral n) as
    | otherwise
    = pure Nothing
  go (SWP m) as
    | i <- fromIntegral m
    , i < length as
    = pure $ Just $ [as !! i] ++ drop 1 (take i as) ++ [as !! (0 ∷ Integer)] ++ drop (i+1) as
    | otherwise
    = pure Nothing
  go (CUP m) as
    | fromIntegral m < length as
    = pure $ Just $ (as !! m):as
    | otherwise
    = pure Nothing
  go (RUN k (SomeRoutine @r _)) as0
    = foldl' (\as _ → as >>= runMaybe) (pure $ Just as0) [0..k-1]
   where
    runMaybe Nothing = pure Nothing
    runMaybe (Just as) = traceM r write simplify as
  go (CLU p i) as
    = pure $ runOp p i as

class (Num a, BitPack a, Show a, NFData a) ⇒ CalculatorNum a where
  add ∷ ECPrime → a → a → a
  sub ∷ ECPrime → a → a → a
  mul ∷ ECPrime → a → a → a
  inv ∷ ECPrime → a → a → a
  bit ∷           a → a → a

runOp ∷ forall a. CalculatorNum a ⇒  ECPrime → CluInstruction → [a] → Maybe [a]
runOp p Calc.Add (a:b:as) = Just $ (add p b a):as
runOp p Calc.Sub (a:b:as) = Just $ (sub p b a):as
runOp p Calc.Inv (a:b:as) = Just $ (inv p b a):as
runOp p Calc.Mul (a:b:as) = Just $ (mul p b a):as
runOp _ Calc.Bit (a:b:as) = Just $ (bit b a):as
runOp _ _        _        = Nothing

data SymbolicNum l r where
  Lit ∷ l → SymbolicNum l r
  Add ∷ r → r → SymbolicNum l r
  Sub ∷ r → r → SymbolicNum l r
  Mul ∷ r → r → SymbolicNum l r
  Inv ∷ r → r → SymbolicNum l r
  Bit ∷ r → r → SymbolicNum l r
  deriving (Eq, Functor, Generic, NFData)

data Fix f
  = Fix (f (Fix f))

deriving instance (forall r . Eq r ⇒ Eq (f r)) ⇒ Eq (Fix f)
deriving instance Generic (Fix f)
deriving instance (forall r . NFData r ⇒ NFData (f r)) ⇒ NFData (Fix f)

data FixChoice l r
  = FixLeft (l (FixChoice l r))
  | FixRight (r (FixChoice l r))

deriving instance (forall r . Eq r ⇒ Eq (f r), forall r . Eq r ⇒ Eq (g r)) ⇒ Eq (FixChoice f g)
deriving instance Generic (FixChoice f g)
deriving instance (forall r . NFData r ⇒ NFData (f r), forall r . NFData r ⇒ NFData (g r)) ⇒ NFData (FixChoice f g)

simplifyFix ∷ (forall r . Eq r ⇒ Eq (f r), Functor f) ⇒ (Fix f → Fix f) → Fix f → Fix f
simplifyFix f x0
  | x' == x0  = x0
  | otherwise = simplifyFix f x'
 where
  x = f x0
  x' | Fix fix <- x = Fix $ fmap (simplifyFix f) fix

simplifyFixChoice ∷
  ( forall r . Eq r ⇒ Eq (f r)
  , forall r . Eq r ⇒ Eq (g r)
  , Functor f, Functor g
  ) ⇒
  (FixChoice f g → FixChoice f g) →
  FixChoice f g → FixChoice f g
simplifyFixChoice f x0
  | x' == x0  = x0
  | otherwise = simplifyFixChoice f x'
 where
  x = f x0
  x' | FixLeft  l <- x = FixLeft  $ fmap (simplifyFixChoice f) l
     | FixRight r <- x = FixRight $ fmap (simplifyFixChoice f) r

instance (Show l, Show r) ⇒ Show (SymbolicNum l r) where
  showsPrec p = \case
    Lit l   → showsPrec p l
    Add x y → showParen (p > 6) $ showsPrec 6 x . showString " + " . showsPrec 7 y
    Sub x y → showParen (p > 6) $ showsPrec 6 x . showString " - " . showsPrec 7 y
    Mul x y → showParen (p > 7) $ showsPrec 7 x . showString " · " . showsPrec 8 y
    Bit x n → showParen (p > 9) $ showsPrec 11 x . showString "[" . showsPrec 0 n . showString "]"
    Inv x z → showParen (p > 1) $ showsPrec 9 x . showString "⁻¹ or " . showsPrec 2 z

instance (forall r . Show r ⇒ Show (f r)) ⇒ Show (Fix f) where
  showsPrec p (Fix x) = showsPrec p x

instance
  ( forall r . Show r ⇒ Show (f r)
  , forall r . Show r ⇒ Show (g r)
  ) ⇒ Show (FixChoice f g)
 where
  showsPrec p (FixLeft f)  = showsPrec p f
  showsPrec p (FixRight g) = showsPrec p g

instance Num l ⇒ Num (Fix (SymbolicNum l)) where
  fromInteger = Fix . Lit . fromInteger
  x + y = Fix $ x `Add` y
  x - y = Fix $ x `Sub` y
  x * y = Fix $ x `Mul` y
  abs = error "unsupported"
  signum = error "unsupported"

instance Num l ⇒ Num (FixChoice (SymbolicNum l) r) where
  fromInteger = FixLeft . Lit . fromInteger
  x + y = FixLeft $ x `Add` y
  x - y = FixLeft $ x `Sub` y
  x * y = FixLeft $ x `Mul` y
  abs = error "unsupported"
  signum = error "unsupported"

instance BitPack (Fix (SymbolicNum l)) where
  type BitSize (Fix (SymbolicNum l)) = 0
  pack = error "unsupported"
  unpack = error "unsupported"

instance BitPack (FixChoice (SymbolicNum l) r) where
  type BitSize (FixChoice (SymbolicNum l) r) = 0
  pack = error "unsupported"
  unpack = error "unsupported"

instance (Show l, Num l, Eq l, NFData l) ⇒
 CalculatorNum (Fix (SymbolicNum l)) where
  add _ x y = Fix $ x `Add` y
  sub _ x y = Fix $ x `Sub` y
  mul _ x y = Fix $ x `Mul` y
  inv _ x z = Fix $ Inv x z
  bit x b   = Fix $ Bit x b

instance (Show l, Num l, Eq l, NFData l, forall r . Show r ⇒ Show (f r),
 forall r . NFData r => NFData (f r)) ⇒
 CalculatorNum (FixChoice (SymbolicNum l) f) where
  add _ x y = FixLeft $ x `Add` y
  sub _ x y = FixLeft $ x `Sub` y
  mul _ x y = FixLeft $ x `Mul` y
  inv _ x z = FixLeft $ Inv x z
  bit x b   = FixLeft $ Bit x b
