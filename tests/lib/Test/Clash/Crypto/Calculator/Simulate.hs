{-|
Module      : Test.Clash.Crypto.Calculator.Simulate
Copyright   : Copyright © 2025-2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Routines to simulate and trace a routine, by recursively executing the
required instructions. Also offers types to support symbolic execution.
-}

{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Clash.Crypto.Calculator.Simulate
  ( run
  , traceM
  , CalculatorNum(..)
  , SymbolicNum(..)
  , Fix(..)
  , simplifyFix
  , FixChoice(..)
  , simplifyFixChoice
  ) where

import Prelude

import Clash.Class.BitPack (BitPack(..))
import Clash.Promoted.Nat (natToNum)
import Control.DeepSeq (NFData(..))
import Data.Functor.Identity (Identity(..))
import Data.List (genericIndex)
import Data.Kind (Type)
import GHC.Generics (Generic)
import GHC.TypeNats (Nat, KnownNat)

import Clash.Crypto.Calculator.ISA
  ( KnownRoutine(..)
  , RoutineFacts(..)
  , Instruction(..)
  , RequiredStackSize
  , CluInstruction
  , KnownInstruction(..)
  , KnownCluInstruction(..)
  , RepetitionBound
  , RequiredStackSize
  )

import qualified Clash.Crypto.Calculator.ISA as Calc

-- | Run a known routine @r@ given a stack of 'CalculatorNum' values. The result
-- is optional, since the routine may underflow the stack. Note that although
-- this function requires @SimulateInstructions@, this constraint is implied
-- under the condition that:
--
-- * @KnownRoutine r@ holds, which is also required by this function;
-- * The structure of @Instructions r@ is completely known, i.e. we can match
--   the entire structure of the list @Instructions r@, and each element of each
--   instruction is known via 'KnownNat', 'KnownRoutine' or
--   'KnownCluInstruction'. This is required by the standard instances of
--   'KnownInstruction' and 'KnownInstructions', so it should automatically
--   follow from there being a 'KnownRoutine' instance.
run ∷
  ∀ r →
  ( Show k
  , KnownRoutine (r ∷ k)
  , CalculatorNum a
  , SimulateInstructions (StackParams is rbound stackSize a)
  , is ~ Instructions r
  , rbound ~ RepetitionBound r
  , stackSize ~ RequiredStackSize r
  ) ⇒ CalculatorNum a ⇒ [a] → Maybe [a]
run r as = runIdentity $ traceM r (const $ pure ()) id as

-- | Run a known routine @r@ given a stack of 'CalculatorNum' values, outputting
-- the state of the stack and the executed instructions along the way.
-- Additionally the elements of the stack are simplified using a supplied
-- function at each step, which can be easily constructed using 'simplifyFix' or
-- 'simplifyFixChoice' in the case that @a@ is constructed as a fixpoint.
traceM ∷
  ∀ {k} m a is rbound stackSize .
  ∀ r →
  ( Show k
  , KnownRoutine (r ∷ k)
  , CalculatorNum a
  , Monad m
  , SimulateInstructions (StackParams is rbound stackSize a)
  , is ~ Instructions r
  , rbound ~ RepetitionBound r
  , stackSize ~ RequiredStackSize r
  ) ⇒ CalculatorNum a ⇒ (String → m ()) → (a → a) → [a] → m (Maybe [a])
traceM r write simplify as
  | RoutineFacts ← knownRoutine @_ @r @a
  = traceInstructionsM
    (StackParams (Instructions r) (RepetitionBound r) (RequiredStackSize r) a)
    write
    simplify
    as

data StackParams
  (is ∷ k)
  (rbound ∷ Nat)
  (stackSize ∷ Nat)
  (a ∷ Type)

class SimulateInstructions (r ∷ k) where
  traceInstructionsM ∷
    ∀ x → x ~ r ⇒
    (CalculatorNum a, Monad m) ⇒
    (String → m ()) → (a → a) → [a] → m (Maybe [a])

instance
  SimulateInstructions (StackParams '[] rbound stackSize a)
 where
  traceInstructionsM _ write _ as = do
    write $ showStack $ Just as
    pure $ Just as

instance
  ( KnownInstruction rbound stackSize a (i ∷ Instruction k Nat Nat Nat Nat Nat)
  , Show k, Show a
  , SimulateInstructions (StackParams i rbound stackSize a)
  , SimulateInstructions (StackParams is rbound stackSize a)
  ) ⇒
  SimulateInstructions (StackParams (i : is) rbound stackSize a)
 where
  traceInstructionsM _ write simplify as = do
    write $ showStack $ Just as
    write $ show $ instruction @_ @rbound @stackSize @a i
    as1 ← traceInstructionsM (StackParams i rbound stackSize a)
            (const $ pure ()) simplify as
    case as1 of
      Nothing  → return Nothing
      Just as2 → do
        let as3 = fmap simplify as2
        ret ← traceInstructionsM (StackParams is rbound stackSize a)
                write simplify as3
        rnf ret `seq` return ret

instance
  KnownNat c ⇒
  SimulateInstructions (StackParams (PUT c) rbound stackSize a)
 where
  traceInstructionsM _ _ _ as = pure $ Just (natToNum @c : as)

instance
  KnownNat n ⇒
  SimulateInstructions (StackParams (POP n) rbound stackSize a)
 where
  traceInstructionsM _ _ _ as
    | i ← natToNum @n
    , i <= length as
    = pure $ Just $ drop i as
    | otherwise
    = pure Nothing

instance
  KnownNat m ⇒
  SimulateInstructions (StackParams (SWP m) rbound stackSize a)
 where
  traceInstructionsM _ _ _ as
    | i ← natToNum @m
    , i < length as
    = pure $ Just $ [genericIndex as i]
                 <> drop 1 (take i as)
                 <> [genericIndex as (0 ∷ Integer)]
                 <> drop (i + 1) as
    | otherwise
    = pure Nothing

instance
  KnownNat m ⇒
  SimulateInstructions (StackParams (CUP m) rbound stackSize a)
 where
  traceInstructionsM _ _ _ as
    | i ← natToNum @m
    , i < length as
    = pure $ Just $ genericIndex as i : as
    | otherwise
    = pure Nothing

instance
  ( Show k
  , KnownRoutine (r ∷ k)
  , CalculatorNum a
  , ∀ a' . CalculatorNum a' ⇒
    SimulateInstructions (StackParams is rbound' stackSize' a')
  , is ~ Instructions r
  , rbound' ~ RepetitionBound r
  , stackSize' ~ RequiredStackSize r
  , KnownNat n
  ) ⇒
  SimulateInstructions (StackParams (RUN n r) rbound stackSize a)
 where
  traceInstructionsM _ write simplify as0 =
    foldl'
      (\as _ → as >>= runMaybe)
      (pure $ Just as0)
      [0 .. natToNum @n @Integer - 1]
   where
    runMaybe Nothing = pure Nothing
    runMaybe (Just as)
      | RoutineFacts ← knownRoutine @_ @r @a
      = traceM r write simplify as

instance
  (KnownNat p, KnownCluInstruction i) ⇒
  SimulateInstructions (StackParams (CLU p i) rbound stackSize a)
 where
  traceInstructionsM _ _ _ as =
    pure $ runOp (natToNum @p) (cluInstruction i) as

showStack ∷ Show a ⇒ Maybe [a] → String
showStack = \case
  Nothing → "↯ Underflow ↯"
  Just [] → "∅ Empty ∅"
  Just as → unwords $ map (flip (showsPrec 11) "") as

-- | Number that supports the operations required for the CLU.
class (Num a, BitPack a, Show a, NFData a) ⇒ CalculatorNum a where
  add ∷ a → a → a → a
  sub ∷ a → a → a → a
  mul ∷ a → a → a → a
  inv ∷ a → a → a → a
  bit ∷     a → a → a

runOp ∷ ∀ a. CalculatorNum a ⇒  a → CluInstruction → [a] → Maybe [a]
runOp p Calc.Add (a:b:as) = Just $ add p b a : as
runOp p Calc.Sub (a:b:as) = Just $ sub p b a : as
runOp p Calc.Inv (a:b:as) = Just $ inv p b a : as
runOp p Calc.Mul (a:b:as) = Just $ mul p b a : as
runOp _ Calc.Bit (a:b:as) = Just $ bit b a   : as
runOp _ _        _        = Nothing

-- | 'CalculatorNum' type that suspends the computation as a structural formula
-- instead. It is meant to be applied to a fixpoint combinator, which ensures
-- that the 'Functor' instance finds all recursion points in the formula.
data SymbolicNum l r where
  Lit ∷ l → SymbolicNum l r
  Add ∷ r → r → SymbolicNum l r
  Sub ∷ r → r → SymbolicNum l r
  Mul ∷ r → r → SymbolicNum l r
  Inv ∷ r → r → SymbolicNum l r
  Bit ∷ r → r → SymbolicNum l r
  deriving (Eq, Functor, Generic, NFData)

-- | Type-level fixpoint combinator.
data Fix f
  = Fix (f (Fix f))

deriving instance (∀ r . Eq r ⇒ Eq (f r)) ⇒ Eq (Fix f)
deriving instance Generic (Fix f)
deriving instance (∀ r . NFData r ⇒ NFData (f r)) ⇒ NFData (Fix f)

-- | Type-level fixpoint combinator with choice.
data FixChoice l r
  = FixLeft (l (FixChoice l r))
  | FixRight (r (FixChoice l r))

deriving instance Generic (FixChoice f g)

deriving instance
  (∀ r . Eq r ⇒ Eq (f r), ∀ r . Eq r ⇒ Eq (g r)) ⇒
  Eq (FixChoice f g)

deriving instance
  (∀ r . NFData r ⇒ NFData (f r), ∀ r . NFData r ⇒ NFData (g r)) ⇒
  NFData (FixChoice f g)

-- | Apply a given function at all recursion points of a fixpoint until
-- exhaustion, i.e. until the result no longer changes.
simplifyFix ∷
  (∀ r . Eq r ⇒ Eq (f r), Functor f) ⇒
  (Fix f → Fix f) → Fix f → Fix f
simplifyFix f x0
  | x' == x0  = x0
  | otherwise = simplifyFix f x'
 where
  x = f x0
  x' | Fix fix ← x = Fix $ fmap (simplifyFix f) fix

-- | Apply a given function at all recursion points of a fixpoint until
-- exhaustion, i.e. until the result no longer changes.
simplifyFixChoice ∷
  ( ∀ r . Eq r ⇒ Eq (f r)
  , ∀ r . Eq r ⇒ Eq (g r)
  , Functor f, Functor g
  ) ⇒
  (FixChoice f g → FixChoice f g) →
  FixChoice f g → FixChoice f g
simplifyFixChoice f x0
  | x' == x0  = x0
  | otherwise = simplifyFixChoice f x'
 where
  x = f x0
  x' | FixLeft  l ← x = FixLeft  $ fmap (simplifyFixChoice f) l
     | FixRight r ← x = FixRight $ fmap (simplifyFixChoice f) r

instance (Show l, Show r) ⇒ Show (SymbolicNum l r) where
  showsPrec p = \case
    Lit l   → showsPrec p l
    Add x y → ip 6 6  x $ showString " + " . showsPrec 7 y
    Sub x y → ip 6 6  x $ showString " - " . showsPrec 7 y
    Mul x y → ip 7 7  x $ showString " · " . showsPrec 8 y
    Bit x n → ip 9 11 x $ showString "[" . shows n . showString "]"
    Inv x z → ip 1 9  x $ showString "⁻¹ or " . showsPrec 2 z
   where
    ip n m x g = showParen (p > n) $ showsPrec m x . g

instance (∀ r . Show r ⇒ Show (f r)) ⇒ Show (Fix f) where
  showsPrec p (Fix x) = showsPrec p x

instance
  ( ∀ r . Show r ⇒ Show (f r)
  , ∀ r . Show r ⇒ Show (g r)
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
  bit   x b = Fix $ Bit x b

instance
  ( Show l, Num l, Eq l, NFData l
  , ∀ r . Show r ⇒ Show (f r)
  , ∀ r . NFData r ⇒ NFData (f r)
  ) ⇒ CalculatorNum (FixChoice (SymbolicNum l) f)
 where
  add _ x y = FixLeft $ x `Add` y
  sub _ x y = FixLeft $ x `Sub` y
  mul _ x y = FixLeft $ x `Mul` y
  inv _ x z = FixLeft $ Inv x z
  bit   x b = FixLeft $ Bit x b
