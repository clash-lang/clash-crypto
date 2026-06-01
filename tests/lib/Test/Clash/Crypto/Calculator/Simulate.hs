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
  , SimInstructions
  , SimulateInstructions(..)
  , StackParams
  ) where

import Prelude
import Clash.Prelude.Safe (Unsigned, Resize(..), testBit)

import Clash.Class.BitPack (BitPack(..))
import Clash.Promoted.Nat (natToNum)
import Control.DeepSeq (NFData(..))
import Data.Functor.Identity (Identity(..))
import Data.List (genericIndex)
import Data.Kind (Type)
import GHC.Generics (Generic)
import GHC.TypeNats (Nat, KnownNat, type (*))

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

-- | Runs a known routine @r@ given a stack of 'CalculatorNum' values. The
-- result is optional, since the routine may underflow the stack. Note that
-- although this function requires 'SimulateInstructions', this constraint is
-- implied under the condition that:
--
-- * @'KnownRoutine' r@ holds, which is also required by this function;
-- * The structure of @'Instructions' r@ is completely known, i.e. we can match
--   the entire structure of the list @'Instructions' r@, and each element of each
--   instruction is known via 'KnownNat', 'KnownRoutine' or
--   'KnownCluInstruction'. This is required by the standard instances of
--   'KnownInstruction' and 'Clash.Crypto.Calculator.ISA.KnownInstructions', so
--   it should automatically follow from there being a 'KnownRoutine' instance.
run ∷
  (Show k, CalculatorNum a) ⇒
  ∀ r → (KnownRoutine (r ∷ k), SimInstructions r a) ⇒
  [a]
  -- ^ value stack
  → Maybe [a]
  -- ^ optional result
run r as = runIdentity $ traceM r (const $ pure ()) id as

-- | Run a known routine @r@ given a stack of 'CalculatorNum' values, outputting
-- the state of the stack and the executed instructions along the way.
-- Additionally the elements of the stack are simplified using a supplied
-- function at each step, which can be easily constructed using 'simplifyFix' or
-- 'simplifyFixChoice' in the case that @a@ is constructed as a fixpoint.
traceM ∷
  ∀ {k} m a. (Show k, Monad m, CalculatorNum a) ⇒
  ∀ r → (KnownRoutine (r ∷ k), SimInstructions r a) ⇒
  (String → m ()) →
  -- ^ monad specific printer
  (a → a) →
  -- ^ simplification function
  [a] →
  -- ^ value stack
  m (Maybe [a])
  -- ^ optional result
traceM r write simplify as
  | RoutineFacts ← knownRoutine @_ @r @a
  = traceInstructionsM
    (StackParams (Instructions r) (RepetitionBound r) (RequiredStackSize r) a)
    write
    simplify
    as

-- | Type alias for simulation instructions over 'StackParams'.
type SimInstructions r a =
  SimulateInstructions
    (StackParams (Instructions r) (RepetitionBound r) (RequiredStackSize r) a)

-- | Symbolic stack parameters.
data StackParams
  (is ∷ k)
  (rbound ∷ Nat)
  (stackSize ∷ Nat)
  (a ∷ Type)

-- | The class of instructions that are symbolically executable.
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

-- | The class of numbers that support CLU operations.
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

-- | A data type variant of 'CalculatorNum', which suspends the
-- computation as a structural formula instead. It is meant to be
-- applied to a fixpoint combinator, which ensures that the 'Functor'
-- instance finds all recursion points in the formula.
data SymbolicNum l r where
  Lit ∷ l → SymbolicNum l r
  Add ∷ r → r → SymbolicNum l r
  Sub ∷ r → r → SymbolicNum l r
  Mul ∷ r → r → SymbolicNum l r
  Inv ∷ r → r → SymbolicNum l r
  Bit ∷ r → r → SymbolicNum l r
  deriving (Eq, Functor, Generic, NFData)

-- | A type-level fixpoint combinator.
data Fix f
  = Fix (f (Fix f))

deriving instance (∀ r . Eq r ⇒ Eq (f r)) ⇒ Eq (Fix f)
deriving instance Generic (Fix f)
deriving instance (∀ r . NFData r ⇒ NFData (f r)) ⇒ NFData (Fix f)

-- | A type-level fixpoint combinator with choice.
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
  (Functor f, ∀ r. Eq r ⇒ Eq (f r)) ⇒
  (Fix f → Fix f) →
  Fix f →
  Fix f
simplifyFix f x0
  | x' == x0  = x0
  | otherwise = simplifyFix f x'
 where
  x = f x0
  x' | Fix fix ← x = Fix $ fmap (simplifyFix f) fix

-- | Apply a given function at all recursion points of a fixpoint until
-- exhaustion, i.e. until the result no longer changes.
simplifyFixChoice ∷
  ( Functor f, ∀ r. Eq r ⇒ Eq (f r)
  , Functor g, ∀ r. Eq r ⇒ Eq (g r)
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

instance CalculatorNum (Unsigned 256) where
  add p x y
   | p - x > y = x + y
   | otherwise = y - (p - x)
  sub p x y
   | x >= y    = x - y
   | otherwise = p - (y - x)
  mul p x y = truncateB $ bigR `mod` extend p
   where
    bigR ∷ Unsigned 512
    bigR = extend x * extend y
  inv p a b =
   if a == 0 then b
   else moduloPower p (p - 2) a 1
  bit a j
   | j < 256, testBit a (fromEnum j) = 1
   | otherwise = 0

moduloPower ∷
  ∀ p. KnownNat p ⇒
  Unsigned p →
  Unsigned p →
  Unsigned p →
  Unsigned p →
  Unsigned p
moduloPower _ 0 _   _   = 1
moduloPower p 1 val tmp = truncateB $ r `mod` extend p
 where
  r ∷ Unsigned (p * 2)
  r = extend val * extend tmp
moduloPower p n val tmp =
 if even n then
  moduloPower p (n `div` 2) (truncateB $ r1 `mod` extend p) (tmp `mod` p)
 else
  moduloPower p (n - 1) val (truncateB $ r2 `mod` extend p)
 where
  r1, r2 ∷ Unsigned (p * 2)
  r1 = extend val * extend val
  r2 = extend tmp * extend val
