{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Clash.Crypto.ECDSA.Routines where

import Clash.Prelude hiding (Mod)
import Clash.Class.Counter (Counter(..))

import Data.Type.Ord (Compare)

import Clash.Crypto.Calculator.ISA

-- TODO
data EcdsaRoutines
  = Main
  | Increment
  | Inc3
  deriving (Generic, NFDataX, BitPack, Show, Ord, Eq)

-- important: the 'Compare' instance is strictly required
type instance Compare (a ∷ EcdsaRoutines) (b ∷ EcdsaRoutines) =
  Compare (RoutineIndex a) (RoutineIndex b)
type RoutineIndex ∷ EcdsaRoutines → Nat
type family RoutineIndex r = n | n → r
 where
  RoutineIndex Main      = 0
  RoutineIndex Increment = 1
  RoutineIndex Inc3      = 2

instance KnownRoutine Main where
  routine _ = Main
  knownRoutine = RoutineFacts
  type Instructions Main =
    '[ POP 3
     , PUT 1
     , PUT 0
     , PUT 3
     , PUT 4
     , PUT 5
     , RUN 1 Increment
     , ADD SecP256ModPrime
     , RUN 2 Inc3
     , POP 1
     , PUT 7
     , CUP 0
     , SUB SecP256ModPrime
     , PUT 8
     , MUL SecP256ModPrime
     , CUP 2
     , INV SecP256ModPrime
     ]

instance KnownRoutine Increment where
  routine _ = Increment
  knownRoutine = RoutineFacts
  type Instructions Increment =
    '[ PUT 1
     , ADD SecP256ModPrime
     ]

instance KnownRoutine Inc3 where
  routine _ = Inc3
  knownRoutine = RoutineFacts
  type Instructions Inc3 =
    '[ RUN 3 Increment
     ]

-- we should make use of type indexed sums here at some point
data EcdsaInstructionPointer
  = EndOfSequence
  | RIPMain      (RIndex Main Main)
  | RIPIncrement (RIndex Main Increment)
  | RIPInc3      (RIndex Main Inc3)
  deriving (Generic, NFDataX)

instance InstructionPointer (Main ∷ EcdsaRoutines) EcdsaInstructionPointer where
  inc _ = \case
    RIPMain n      | (False, m) ← countSuccOverflow n → RIPMain m
    RIPIncrement n | (False, m) ← countSuccOverflow n → RIPIncrement m
    RIPInc3 n      | (False, m) ← countSuccOverflow n → RIPInc3 m
    _ → EndOfSequence

  start _ = \case
    Main
      | USucc{} ← toUNat (SNat @(InstructionCount Main))
      → RIPMain . RIndex 0

    Increment
      | USucc{} ← toUNat (SNat @(InstructionCount Increment))
      → RIPIncrement . RIndex 0

    Inc3
      | USucc{} ← toUNat (SNat @(InstructionCount Inc3))
      → RIPInc3 . RIndex 0

  instr @a _ = \case
    RIPMain RIndex{..}
      | RoutineFacts ← knownRoutine @_ @Main @a
      → pure $ instructions' Main Main !! iptr

    RIPIncrement RIndex{..}
      | RoutineFacts ← knownRoutine @_ @Increment @a
      → pure $ instructions' Main Increment !! iptr

    RIPInc3 RIndex{..}
      | RoutineFacts ← knownRoutine @_ @Inc3 @a
      → pure $ instructions' Main Inc3 !! iptr

    _ → Nothing
