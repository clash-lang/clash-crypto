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

import Data.Kind (Type)

import Clash.Promoted.Integer
import Clash.Promoted.List

import Clash.Crypto.Calculator.Modulo (Mod)

--------------------------------------------------------------------------------

-- | Calculator Instructions
--
-- Requires the `n`, `m` and `k` parameters to all have 'Num' instances
-- and the `a` parameter to have both 'BitPack' and 'Num' instances.
data Instruction r n m k p a
  = -- | pushes the given constant to the stack
    PUT a
  | -- | pops n elements from the stack
    POP n
  | -- | swaps the n-th element on the stack with the top element
    SWP m
  | -- | pushes a copy of the n-th element on the stack to the top of
    -- the stack
    CUP m
  | -- | runs a given subroutine consisting of a fixed finite sequence
    -- of instructions `k` times
    RUN k r
  | -- | runs the given CLU instruction in the prime field p
    CLU p CluInstruction
  deriving
    ( Generic, NFDataX, Eq, Ord, Show )

deriving instance
  ( BitPack r, BitPack n, BitPack m, BitPack k, BitPack p, BitPack a
  , 1 ≤ BitSize a
  ) ⇒ BitPack (Instruction r n m k p a)

-- | Crypto Logic Unit Instructions
--
-- All CLU instructions use the top two elements on the stack as
-- operands and replace them by the result of the computation, i.e.,
-- the number of elements on the stack decreases by one after the
-- instruction has been executed.
data CluInstruction
  = Add
    -- ^ adds the top two elements on the stack
  | Sub
    -- ^ subtracts the top element on the stack from the below-top one
  | Inv
    -- ^ if the below-top element is non-zero, then the top two
    -- elements are replaced by its modulo inverse; otherwise they are
    -- replaced by the unmodified top element
  | Mul
    -- ^ multiplies the top two elements on the stack
  | Bit
    -- ^ pushes the `n`-th bit of the below-top element onto the stack
    -- using the top element as the index `n` with zero indexing the
    -- least significant bit; pushes `0` if the given index points
    -- beyond the utilized bit width
  deriving (Generic, NFDataX, BitPack, Ord, Eq, Enum, Bounded, Show)

--------------------------------------------------------------------------------

-- | Reification of type-level 'CluInstruction's.
class KnownCluInstruction (instr ∷ CluInstruction)
 where
   cluInstruction ∷ ∀ x → x ~ instr ⇒ CluInstruction

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

-- | A finite space to distinguish between the supported elliptic
-- curve primes.
data ECPrime
  = SecP256Mod
  | SecP256Ord
  deriving (Generic, NFDataX, BitPack, Ord, Eq, Enum, Bounded, Show)

-- | Maps the 'ECPrime' reference to the actual prime.
type family CPrime (p :: ECPrime) ∷ Nat where
  CPrime SecP256Mod = SecP256ModPrime
  CPrime SecP256Ord = SecP256OrdPrime

type CMod p = Mod (CPrime p)
type ECMod = CMod SecP256Mod

--------------------------------------------------------------------------------

-- | Reified type of an 'Instruction' at the term-level.
type Instr group (rbound ∷ Nat) (stackSize ∷ Nat) (a ∷ Type) =
  Instruction
    group
    (Index (stackSize + 1))
    (Index stackSize)
    (Index rbound)
    ECPrime
    a

-- | Identifies all instruction sequences that can be reified.
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

-- | The reified instruction vector of a routine.
instructions ∷
  ∀ {group} (stackSize ∷ Nat) (a ∷ Type).
  ∀ (main ∷ group) →
  ∀ (routine ∷ group) →
  KnownInstructions (RepetitionBound main) stackSize a (Instructions routine) ⇒
  Vec (InstructionCount routine)
    (Instr group (RepetitionBound main) stackSize a)
instructions _ r = instructionVec (Instructions r)

--------------------------------------------------------------------------------

-- | Links a type-level list of instructions with a routine reference
-- and all derivable proofs. Furthermore supports term-level
-- reification of the provided reference.
class KnownRoutine (routine ∷ group) where

  -- | The linked type-level list of instructions
  type Instructions routine ∷ [Instruction group Nat Nat Nat Nat Nat]

  -- | All proven facts that are derivable from the given routine.
  knownRoutine ∷ (Num a, BitPack a) ⇒ RoutineFacts routine a

  -- | The reified term matching the given type.
  routine ∷ ∀ x → x ~ routine ⇒ group

-- | Identifies the types that can serve as instruction pointers for
-- particular routines supporting the operations associated with the
-- class.
class InstructionPointer (main ∷ group) ptr where
  -- | Every instruction pointer can be incremented.
  inc ∷ ∀ x → x ~ main ⇒ ptr → ptr

  -- | An instruction pointer has a dedicated start value.
  start ∷ ∀ x → x ~ main ⇒ group → Index (RepetitionBound main) → ptr

  -- | A routine + instruction pointer determines the particular
  -- instruction to be executed. Returns `Nothing` after reaching the
  -- end of the instruction sequence associated with the routine.
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

-- | A convenience type for defining instruction pointers.
data RIndex (main ∷ group) (subroutine ∷ group) = RIndex
  { -- | The particular position being pointed to in the sequence
    -- associated with the routine.
    iptr ∷ Index (InstructionCount subroutine)
  , -- | The number of rounds a particular subroutine still must
    -- be repeated.
    rbnd ∷ Index (RepetitionBound main)
  }
  deriving (Generic, NFDataX, Show)

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

-- | All evidence that can be derived automatically for a known
-- routine.
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

class    KnownNat (RepetitionBound r)   ⇒ KnownRepetitionBound r
instance KnownNat (RepetitionBound r)   ⇒ KnownRepetitionBound r

-- | Lists all the subroutines of a routine, along with the routine
-- itself.
type Routines routine = routine : SubRoutines routine
type InstructionCount routine = Length (Instructions routine)
type SubRoutineCount routine = Length (SubRoutines routine)

-- | Lists all the subroutines of a routine.
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

-- | Retrieves the maximum length of the instruction sequences
-- utilized by a given routine.
type InstructionBound routine = InstructionBound# 0 (Routines routine)
type InstructionBound# ∷ ∀ routine. Nat → [routine] → Nat
type family InstructionBound# n rs
 where
  InstructionBound# n '[]      = n
  InstructionBound# n (x : xr) =
    InstructionBound# (Max n (InstructionCount x)) xr

-- | Retrieves the maximum number of iterations of all subroutines
-- utilized by the given routine.
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

-- | Retrieves the stack requirement profile for a given routine.
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

-- | The number of arguments being read from the stack.
type ArgCount routine = ArgCount# (GetProfile routine)
type ArgCount# ∷ StackProfile → Nat
type family ArgCount# p
 where
  ArgCount# ('StackProfile _ _ l) = l

-- | The number of results remaining on the stack after execution.
type ResultCount routine = ResultCount# (GetProfile routine)
type ResultCount# ∷ StackProfile → Nat
type family ResultCount# p
 where
  ResultCount# ('StackProfile p _ l) = Abs (Toℤ l .+. p)

-- | The maximum stack size needed to run a routine and all its
-- subroutines.
type RequiredStackSize routine = RequiredStackSize# (GetProfile routine)
type RequiredStackSize# ∷ StackProfile → Nat
type family RequiredStackSize# p
 where
  RequiredStackSize# ('StackProfile _ u l) = u + l

-- | The folding function utilized by 'GetProfile'.
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

-- | Combines the stack profile of a subroutine with the one of the
-- calling routine.
type Attach ∷ Nat → StackProfile → StackProfile → StackProfile
type family Attach k a b
 where
  Attach 0 s _ = s
  Attach k ('StackProfile p0 u0 l0) ('StackProfile p1 u1 l1) =
    'StackProfile
      (p0 .+. (Toℤ k .*. p1))
      (Maxℤ (Maxℤ u0 (Toℤ u1)) (p0 .+. ((Dec (Toℤ k)) .*. p1) .+. Toℤ u1))
      (Minℤ (Minℤ l0 (Toℤ l1)) (p0 .+. ((Dec (Toℤ k)) .*. p1) .-. Toℤ l1))
