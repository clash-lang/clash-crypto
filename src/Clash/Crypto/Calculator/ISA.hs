{-|
Module      : Clash.Crypto.Calculator.ISA
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Instruction Set Architecture for the calculator.
-}

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoGeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}

module Clash.Crypto.Calculator.ISA where

import Clash.Prelude.Safe hiding (Bit, Mod)
import Clash.Class.Counter (Counter(..))

import Language.Haskell.Unicode (type (≤))

import Data.Kind (Type, Constraint)

import Clash.Promoted.Integer
import Clash.Promoted.List

import Clash.Crypto.ECDSA.Modulo (Mod)

-- | Calculator Instructions
--
-- Requires the `n`, `m` and `k` parameters to have a `Num` instances
-- and the `a` parameter to have a `BitPack` and `Num` instance.
data Instruction r n m k p a
  = PUT a
    -- ^ pushes the given constant to the stack
  | POP n
    -- ^ pops n elements from the stack
  | SWP m
    -- ^ swaps the n-th element on the stack with the top element
  | CUP m
    -- ^ pushes a copy of the n-th element on the stack to the top of
    -- the stack
  | RUN k r
    -- ^ runs a given subroutine consisting of a fixed finite sequence
    -- of instructions `k` times
  | CLU p CluInstruction
    -- ^ runs the given CLU instruction in the prime field p
  deriving (Generic, NFDataX, Eq, Ord, Show)

deriving instance
  ( BitPack r, BitPack n, BitPack m, BitPack k, BitPack p, BitPack a
  , 1 ≤ BitSize a
  ) ⇒ BitPack (Instruction r n m k p a)

--------------------------------------------------------------------------------

-- | Crypto Logic Unit Instructions
--
-- All CLU instructions use the top two elements on the stack as their
-- operands and replace them by the result of the computation, i.e.,
-- the number of elements on the stack decreases by one element when
-- executing the instruction.
data CluInstruction
  = Add
    -- ^ adds the top two elements on the stack
  | Sub
    -- ^ subtracts the top element on the stack from the element after
    -- the top one
  | Inv
    -- ^ places the modulo inverse of the element after the top one on
    -- the stack, unless that element is zero. In the zero case, the
    -- top element is taken instead.
  | Mul
    -- ^ multiplies the top two elements on the stack
  | Bit
    -- ^ places `1` on the stack if the `n`-th bit of the element
    -- after the top one on the stack is set and `0` otherwise; the
    -- index `n` is read from the top of the stack; places a `0` if
    -- `n` is out-of-range
  deriving (Generic, NFDataX, BitPack, Ord, Eq, Enum, Bounded, Show)

type KnownCluInstruction ∷ CluInstruction → Constraint
class KnownCluInstruction ins
 where
   cluInstruction ∷ ∀ x → x ~ ins ⇒ CluInstruction

instance KnownCluInstruction Add where cluInstruction _ = Add
instance KnownCluInstruction Sub where cluInstruction _ = Sub
instance KnownCluInstruction Inv where cluInstruction _ = Inv
instance KnownCluInstruction Mul where cluInstruction _ = Mul
instance KnownCluInstruction Bit where cluInstruction _ = Bit

type ADD p = CLU p Add
type SUB p = CLU p Sub
type MUL p = CLU p Mul
type INV p = CLU p Inv
type BIT p = CLU p Bit

pattern ADD ∷ p → Instruction r n m k p a ; pattern ADD p = CLU p Add
pattern SUB ∷ p → Instruction r n m k p a ; pattern SUB p = CLU p Sub
pattern MUL ∷ p → Instruction r n m k p a ; pattern MUL p = CLU p Mul
pattern INV ∷ p → Instruction r n m k p a ; pattern INV p = CLU p Inv
pattern BIT ∷ p → Instruction r n m k p a ; pattern BIT p = CLU p Bit

{-# COMPLETE PUT, POP, SWP, CUP, RUN, ADD, SUB, MUL, INV, BIT #-}

--------------------------------------------------------------------------------

-- | 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1
type SecP256ModPrime
  = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

-- | 2 ^ 256 - 2 ^ 224 + 2 ^ 192 - 0x4319055258E8617B0C46353D039CDAAF
type SecP256OrdPrime
  = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

data ECPrime
  = SecP256Mod
  | SecP256Ord
  deriving (Generic, NFDataX, BitPack, Ord, Eq, Enum, Bounded, Show)

type family CPrime (p :: ECPrime) ∷ Nat where
  CPrime SecP256Mod = SecP256ModPrime
  CPrime SecP256Ord = SecP256OrdPrime

type CMod p = Mod (CPrime p)
type ECMod = CMod SecP256Mod

--------------------------------------------------------------------------------

type Instr group (rbound ∷ Nat) (stackSize ∷ Nat) (a ∷ Type) =
  Instruction
    group
    (Index (stackSize + 1))
    (Index stackSize)
    (Index rbound)
    ECPrime
    a

class KnownInstructions
  (rbound ∷ Nat)
  (stackSize ∷ Nat)
  (a ∷ Type)
  (instructions ∷ [Instruction group Nat Nat Nat Nat Nat])
 where
  instructionVec ∷
    ∀ x → x ~ instructions ⇒
    Vec (Length instructions) (Instr group rbound stackSize a)

instance
  KnownInstructions b s a '[]
 where
  instructionVec _ = Nil

instance
  (KnownNat c, KnownInstructions b s a is, Num a, BitPack a) ⇒
  KnownInstructions b s a (PUT c : is)
 where
  instructionVec _ = PUT (natToNum @c) :> instructionVec is

instance
  (KnownNat n, KnownNat s, KnownInstructions b s a is) ⇒
  KnownInstructions b s a (POP n : is)
 where
  instructionVec _ = POP (natToNum @n) :> instructionVec is

instance
  (KnownNat n, KnownNat s, KnownInstructions b s a is) ⇒
  KnownInstructions b s a (SWP n : is)
 where
  instructionVec _ = SWP (natToNum @n) :> instructionVec is

instance
  (KnownNat n, KnownNat s, KnownInstructions b s a is) ⇒
  KnownInstructions b s a (CUP n : is)
 where
  instructionVec _ = CUP (natToNum @n) :> instructionVec is

instance
  (KnownRoutine k, KnownNat n, KnownNat b, KnownInstructions b s a is) ⇒
  KnownInstructions b s a (RUN n k : is)
 where
  instructionVec _ = RUN (natToNum @n) (routine k) :> instructionVec is

instance
  (KnownCluInstruction ins, KnownInstructions b s a is) ⇒
  KnownInstructions b s a (CLU SecP256ModPrime ins : is)
 where
  instructionVec _ = CLU SecP256Mod (cluInstruction ins) :> instructionVec is

instance
  (KnownCluInstruction ins, KnownInstructions b s a is) ⇒
  KnownInstructions b s a (CLU SecP256OrdPrime ins : is)
 where
  instructionVec _ = CLU SecP256Ord (cluInstruction ins) :> instructionVec is

instructions ∷
  ∀ {group} (stackSize ∷ Nat) (a ∷ Type).
  ∀ (main ∷ group) →
  ∀ (routine ∷ group) →
  KnownInstructions (RepetitionBound main) stackSize a (Instructions routine) ⇒
  Vec (InstructionCount routine)
    (Instr group (RepetitionBound main) stackSize a)
instructions _ r = instructionVec (Instructions r)

--------------------------------------------------------------------------------

class KnownRoutine (routine ∷ group) where
  type Instructions routine ∷ [Instruction group Nat Nat Nat Nat Nat]
  knownRoutine ∷ (Num a, BitPack a) ⇒ RoutineFacts routine a
  routine ∷ ∀ x → x ~ routine ⇒ group

class InstructionPointer (main ∷ group) ptr where
  inc ∷ ∀ x → x ~ main ⇒ ptr → ptr
  start ∷ ∀ x → x ~ main ⇒ group → Index (RepetitionBound main) → ptr
  instr ∷
    (Num a, BitPack a) ⇒
    ∀ x → x ~ main ⇒
    ptr →
    Maybe (
      Instr group
        (RepetitionBound main)
        (RequiredStackSize main)
        a
      )

data RIndex (main ∷ group) (subroutine ∷ group) = RIndex
  { iptr ∷ Index (InstructionCount subroutine)
  , rbnd ∷ Index (RepetitionBound main)
  }
  deriving (Generic, NFDataX)

-- TODO[investigate]: deriving BitPack currently causes a
--   "solveWanteds: too many iterations" error
--
--deriving instance
--  ( KnownNat (InstructionCount subroutine)
--  , KnownNat (RepetitionBound main)
--  , 1 ≤ InstructionCount subroutine
--  ) ⇒ BitPack (RIndex main subroutine)

instance
  ( KnownNat (RepetitionBound main), KnownNat (InstructionCount subroutine)
  , 1 ≤ InstructionCount subroutine
  ) ⇒
  Counter (RIndex main subroutine)
 where
  countMin = RIndex { iptr = minBound, rbnd = maxBound }
  countMax = RIndex { iptr = maxBound, rbnd = minBound }
  countSuccOverflow i@RIndex{..}
    | iptr < maxBound = (False, i { iptr = iptr + 1 })
    | rbnd > 0        = (False, RIndex { iptr = 0, rbnd = rbnd - 1 })
    | otherwise       = (True, countMin)
  countPredOverflow i@RIndex{..}
    | iptr > minBound = (False, i { iptr = iptr - 1 })
    | rbnd < maxBound = (False, RIndex { iptr = maxBound, rbnd = rbnd + 1 })
    | otherwise       = (True, countMax)

--------------------------------------------------------------------------------

data RoutineFacts (routine ∷ group) (a ∷ Type) where
  RoutineFacts ∷
    ( KnownInstructions
        (RepetitionBound routine)
        (RequiredStackSize routine)
        a
        (Instructions routine)
    , InstanceAll (Routines routine) KnownInstructionCount
    , InstanceAll (Routines routine) KnownSubRoutineCount
    , InstanceAll (Routines routine) KnownArgCount
    , InstanceAll (Routines routine) KnownResultCount
    , InstanceAll (Routines routine) KnownRequiredStackSize
    , InstanceAll (Routines routine) KnownInstructionBound
    , InstanceAll (Routines routine) KnownRepetitionBound
    ) ⇒ RoutineFacts routine a

class    KnownNat (InstructionCount r)  ⇒ KnownInstructionCount r
instance KnownNat (InstructionCount r)  ⇒ KnownInstructionCount r

class    KnownNat (SubRoutineCount r)   ⇒ KnownSubRoutineCount r
instance KnownNat (SubRoutineCount r)   ⇒ KnownSubRoutineCount r

class    KnownNat (ArgCount r)          ⇒ KnownArgCount r
instance KnownNat (ArgCount r)          ⇒ KnownArgCount r

class    KnownNat (ResultCount r)       ⇒ KnownResultCount r
instance KnownNat (ResultCount r)       ⇒ KnownResultCount r

class    KnownNat (RequiredStackSize r) ⇒ KnownRequiredStackSize r
instance KnownNat (RequiredStackSize r) ⇒ KnownRequiredStackSize r

class    KnownNat (InstructionBound r)  ⇒ KnownInstructionBound r
instance KnownNat (InstructionBound r)  ⇒ KnownInstructionBound r

class    KnownNat (RepetitionBound r)  ⇒ KnownRepetitionBound r
instance KnownNat (RepetitionBound r)  ⇒ KnownRepetitionBound r

type Routines routine = routine : SubRoutines routine
type InstructionCount routine = Length (Instructions routine)
type SubRoutineCount routine = Length (SubRoutines routine)

type SubRoutines routine = SubRoutines# '[] (Instructions routine)
type SubRoutines# ∷
  ∀ routine group n m k p a.
  SortedList routine →
  [Instruction group n m k p a] →
  SortedList routine
type family SubRoutines# a xs
 where
  SubRoutines# a (RUN _ s : xr)
    = SubRoutines# (SLInsert s (SLMerge a (SubRoutines s))) xr
  SubRoutines# a (_ : xr) = SubRoutines# a xr
  SubRoutines# a '[] = a

type InstructionBound routine = InstructionBound# 0 (Routines routine)
type InstructionBound# ∷ ∀ routine. Nat → [routine] → Nat
type family InstructionBound# n rs
 where
  InstructionBound# n '[]      = n
  InstructionBound# n (x : xr) =
    InstructionBound# (Max n (InstructionCount x)) xr

type RepetitionBound routine = 1 + RepetitionBound# 0 (Instructions routine)
type RepetitionBound# ∷ Nat → [Instruction group n m k p a] → Nat
type family RepetitionBound# n rs
 where
  RepetitionBound# n '[] = n
  RepetitionBound# n (RUN k r : xr) =
    RepetitionBound# (RepetitionBound# (Max n k) (Instructions r)) xr
  RepetitionBound# n (_: xr) =
    RepetitionBound# n xr

--------------------------------------------------------------------------------

-- | Stack Requirements Profile
data StackProfile = StackProfile
  { -- | relative pointer to the stack starting at zero
    stackPointer ∷ ℤ
    -- | always positive, i.e., we don't need the sign
  , upperBound ∷ Nat
    -- | always negative, i.e., we don't need the sign
  , lowerBound ∷ Nat
  }

type GetProfile routine
  = GetProfile# ('StackProfile (Toℤ 0) 0 0) (Instructions routine)
type GetProfile# ∷
  StackProfile →
  [Instruction group Nat Nat Nat Nat a] →
  StackProfile
type family GetProfile# p is
 where
  GetProfile# p '[] = p
  GetProfile# p (i : is) = GetProfile# (Requirements p i) is

-- | Number of arguments being read from the stack.
type ArgCount routine = ArgCount# (GetProfile routine)
type ArgCount# ∷ StackProfile → Nat
type family ArgCount# p
 where
  ArgCount# ('StackProfile _ _ l) = l

-- | Number of results remaining on the stack after execution.
type ResultCount routine = ResultCount# (GetProfile routine)
type ResultCount# ∷ StackProfile → Nat
type family ResultCount# p
 where
  ResultCount# ('StackProfile p _ l) = Abs (Toℤ l .+. p)

type RequiredStackSize routine = RequiredStackSize# (GetProfile routine)
type RequiredStackSize# ∷ StackProfile → Nat
type family RequiredStackSize# p
 where
  RequiredStackSize# ('StackProfile _ u l) = u + l

type Requirements ∷
  StackProfile →
  Instruction group Nat Nat Nat Nat a →
  StackProfile
type family Requirements p i
 where
   Requirements ('StackProfile p u l) (PUT _) =
     'StackProfile (Inc p) (Maxℤ u (Inc p)) l

   Requirements ('StackProfile p u l) (POP n) =
     'StackProfile (p .-. Toℤ n) u (Minℤ l (p .-. Toℤ n))

   Requirements ('StackProfile p u l) (SWP n) =
     'StackProfile p u (Minℤ l (p .-. Toℤ (n + 1)))

   Requirements ('StackProfile p u l) (CUP n) =
     'StackProfile (Inc p) (Maxℤ u (Inc p)) (Minℤ l (p .-. Toℤ (n + 1)))

   Requirements ('StackProfile p u l) (CLU _ _) =
     'StackProfile (Dec p) u (Minℤ l (p .-. Toℤ 2))

   Requirements p (RUN k r) = Attach k p (GetProfile r)

type Attach ∷ Nat → StackProfile → StackProfile → StackProfile
type family Attach k a b
 where
  Attach 0 s _ = s
  Attach k ('StackProfile p0 u0 l0) ('StackProfile p1 u1 l1) =
    'StackProfile
      (p0 .+. (Toℤ k .*. p1))
      (Maxℤ (Maxℤ u0 (Toℤ u1)) (p0 .+. ((Dec (Toℤ k)) .*. p1) .+. Toℤ u1))
      (Minℤ (Minℤ l0 (Toℤ l1)) (p0 .+. ((Dec (Toℤ k)) .*. p1) .-. Toℤ l1))
