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
{-# LANGUAGE TypeAbstractions #-}

module Clash.Crypto.Calculator.ISA where

import Clash.Prelude.Safe hiding (Bit, Mod)
import Clash.Class.Counter (Counter(..))

import Language.Haskell.Unicode (type (≤))

import Data.Kind (Type)

import Clash.Promoted.Integer
import Clash.Promoted.List

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

--------------------------------------------------------------------------------

-- | Reified type of an 'Instruction' at the term-level.
type Instr group (rbound ∷ Nat) (stackSize ∷ Nat) (a ∷ Type) =
  Instruction
    group
    (Index (stackSize + 1))
    (Index stackSize)
    (Index rbound)
    a
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
  (KnownInstruction b s a i, KnownInstructions b s a is) ⇒
  KnownInstructions b s a (i : is)
 where
  instructionVec _ = instruction i :> instructionVec is

class KnownInstruction
  (rbound ∷ Nat)
  (stackSize ∷ Nat)
  (a ∷ Type)
  (instruction ∷ Instruction group Nat Nat Nat Nat Nat)
 where
  instruction ::
    ∀ x → x ~ instruction ⇒
    Instr group rbound stackSize a

instance
  (KnownNat c, Num a, BitPack a) ⇒
  KnownInstruction b s a (PUT c)
 where
  instruction _ = PUT (natToNum @c)

instance
  (KnownNat n, KnownNat s) ⇒
  KnownInstruction b s a (POP n)
 where
  instruction _ = POP (natToNum @n)

instance
  (KnownNat n, KnownNat s) ⇒
  KnownInstruction b s a (SWP n)
 where
  instruction _ = SWP (natToNum @n)

instance
  (KnownNat n, KnownNat s) ⇒
  KnownInstruction b s a (CUP n)
 where
  instruction _ = CUP (natToNum @n)

instance
  (KnownCluInstruction ins, Num a, KnownNat p) ⇒
  KnownInstruction b s a (CLU p ins)
 where
  instruction _ = CLU (natToNum @p) (cluInstruction ins)

instance
  (KnownRoutine k, KnownNat n, KnownNat b) ⇒
  KnownInstruction b s a (RUN n k)
 where
  instruction _ = RUN (natToNum @n) (routine k)

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

deriving instance
  ( KnownNat (InstructionCount subroutine)
  , KnownNat (RepetitionBound# (Instructions main))
  , 1 ≤ InstructionCount subroutine
  ) ⇒ BitPack (RIndex main subroutine)

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
    , InstanceAll (Routines routine) KnownCallDepth
    , InstanceAll (Routines routine) KnownArgCount
    , InstanceAll (Routines routine) KnownResultCount
    , InstanceAll (Routines routine) KnownRequiredStackSize
    , InstanceAll (Routines routine) KnownRepetitionBound
    ) ⇒ RoutineFacts routine a

class    KnownNat (InstructionCount r)  ⇒ KnownInstructionCount r
instance KnownNat (InstructionCount r)  ⇒ KnownInstructionCount r

class    KnownNat (SubRoutineCount r)   ⇒ KnownSubRoutineCount r
instance KnownNat (SubRoutineCount r)   ⇒ KnownSubRoutineCount r

class    KnownNat (CallDepth r)         ⇒ KnownCallDepth r
instance KnownNat (CallDepth r)         ⇒ KnownCallDepth r

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
type SubRoutines routine = SubRoutines# (Instructions routine)
type SubRoutines# ∷
  ∀ routine group n m k p a.
  [Instruction group n m k p a] →
  SortedList routine
type family SubRoutines# xs
 where
  SubRoutines# (RUN _ r : xr)
    = SLInsert r (SLMerge (SubRoutines r) (SubRoutines# xr))
  SubRoutines# (_ : xr) = SubRoutines# xr
  SubRoutines# '[] = '[]

-- | Retrieves the maximum length of the instruction sequences
-- utilized by a given routine.
type InstructionBound routine = InstructionBound# (Routines routine)
type InstructionBound# ∷ ∀ routine. [routine] → Nat
type family InstructionBound# rs
 where
  InstructionBound# (x : xr) = Max (InstructionCount x) (InstructionBound# xr)
  InstructionBound# '[] = 0

-- | Retrieves the maximum number of iterations of all subroutines
-- utilized by the given routine.
type RepetitionBound routine = 1 + RepetitionBound# (Instructions routine)
type RepetitionBound# ∷ [Instruction group n m k p a] → Nat
type family RepetitionBound# is
 where
  RepetitionBound# (RUN k r : xr) =
    Max k (Max (RepetitionBound# (Instructions r)) (RepetitionBound# xr))
  RepetitionBound# (_ : xr) = RepetitionBound# xr
  RepetitionBound# '[] = 0

-- | Retrieves the depth of the call tree of a given routine.
type CallDepth routine = 1 + CallDepth# (Instructions routine)
type CallDepth# ∷ [Instruction group n m k p a] → Nat
type family CallDepth# is
 where
  CallDepth# (RUN _ r : xr) =
    Max (CallDepth r) (CallDepth# xr)
  CallDepth# (_ : xr) = CallDepth# xr
  CallDepth# '[] = 0

--------------------------------------------------------------------------------

-- | Stack Requirements Profile
data StackProfile = StackProfile
  { -- | a relative pointer to the stack ending at zero
    stackPointer ∷ ℤ
    -- | the upper bound of stack positions accessed relative to zero;
    -- always positive, i.e., it suffices to store the absolute value
  , upperBound ∷ Nat
    -- | the lower bound of stack positions accessed relative to zero;
    -- always negative, i.e., it suffices to store the absolute value
  , lowerBound ∷ Nat
  }

-- | Retrieves the stack requirement profile for a given routine.
type GetProfile routine = GetProfile# (Instructions routine)
type GetProfile# ∷ [Instruction group Nat Nat Nat Nat a] → StackProfile
type family GetProfile# is
 where
  GetProfile# '[] = 'StackProfile (Toℤ 0) 0 0
  GetProfile# (i : is) = Requirements i (GetProfile# is)

-- | The number of arguments being read from the stack.
type ArgCount routine = ArgCount# (GetProfile routine)
type ArgCount# ∷ StackProfile → Nat
type family ArgCount# p
 where
  -- The number of arguments is given by the number of stack addresses
  -- accessed below the initial position of the stack pointer. The
  -- initial position is stored in the profile after evaluating
  -- 'GetProfile'. Hence, the number of arguments is given by the
  -- distance of the initial stack pointer to the lower bound.
  ArgCount# ('StackProfile p _ l) = Abs (p .+. Toℤ l)

-- | The number of results remaining on the stack after execution.
type ResultCount routine = ResultCount# (GetProfile routine)
type ResultCount# ∷ StackProfile → Nat
type family ResultCount# p
 where
  -- The remaining number of results on the stack after execution is
  -- given by the distance of the final stack pointer to the lower
  -- bound. However, the final stack pointer ends at zero by
  -- definition. Hence, the remaining number of results on the stack
  -- is given by the lower bound.
  ResultCount# ('StackProfile _ _ l) = l

-- | The maximum stack size needed to run a routine and all its
-- subroutines.
type RequiredStackSize routine = RequiredStackSize# (GetProfile routine)
type RequiredStackSize# ∷ StackProfile → Nat
type family RequiredStackSize# p
 where
  -- The distance between the lower and upper bounds determines the
  -- required size of the stack.
  RequiredStackSize# ('StackProfile _ u l) = u + l

-- | The folding function utilized by 'GetProfile'.
type Requirements ∷
  Instruction group Nat Nat Nat Nat a →
  StackProfile →
  StackProfile
type family Requirements i p
 where
   -- Note that in all of the calculations below the upper and lower
   -- bounds simply track the stack access maxima resulting from the
   -- operations.
   Requirements (PUT _) ('StackProfile p u l) =
     -- Putting an element onto the stack will increase it by one.
     -- Hence, the pointer before the operation must be one less.
     'StackProfile (Dec p) u (Minℤ l (Dec p))

   Requirements (POP n) ('StackProfile p u l) =
     -- Popping n elements from the stack will decrease it by n. Hence,
     -- the pointer before the operation must be n elements larger.
     'StackProfile (p .+. Toℤ n) (Maxℤ u (p .+. Toℤ n)) l

   Requirements (SWP n) ('StackProfile p u l) =
     -- Swapping the n-th element does not change the pointer, but it
     -- gives evidence about the existence of a swappable element at
     -- the pointer position minus (n + 1), e.g., `SWP 0` is a no-op
     -- while still giving evidence that there must be at least one
     -- element on the stack.
     'StackProfile p u (Minℤ l (p .-. Toℤ (n + 1)))

   Requirements (CUP n) ('StackProfile p u l) =
     -- Copying the n-th element to the top of the stack has the same
     -- profile as first adding a dummy element to the stack [PUT _]
     -- and then swapping the (n + 1)-th element instead [SWP (n + 1)].
     'StackProfile (Dec p) u (Minℤ l (p .-. Toℤ (n + 2)))

   Requirements (CLU _ _) ('StackProfile p u l) =
     -- Executing a CLU operation has the same stack profile as popping
     -- two elements from the stack [POP 2] and then putting a result
     -- afterwards [PUT _]. Note that `Minℤ l (Dec (p .+. Toℤ 2)) ≡ l`
     -- by construction.
     'StackProfile (Inc p) (Maxℤ u (p .+. Toℤ 2)) l

   Requirements (RUN k r) p =
     -- See 'Attach'.
     Attach k p (GetProfile r)

-- | Combines the stack profile of a subroutine with the one of the
-- calling routine.
type Attach ∷ Nat → StackProfile → StackProfile → StackProfile
type family Attach k a b
 where
  -- Not running a routine will not change the stack profile.
  Attach 0 s _ = s
  -- Running a routine k times will move the stack pointer k times
  -- relatively to the stack profile of that routine. The same
  -- principle applies for both extremes.
  Attach k ('StackProfile p0 u0 l0) ('StackProfile p1 u1 l1) =
    'StackProfile
      (p0 .+. (Toℤ k .*. p1))
      (Maxℤ u0 (p0 .+. (Toℤ k .*. p1) .+. Toℤ u1))
      (Minℤ l0 (p0 .+. (Toℤ k .*. p1) .-. Toℤ l1))
