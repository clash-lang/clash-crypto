{-|
Module      : Test.Clash.Crypto.Calculator
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test specifics for 'Clash.Crypto.Calculator'.
-}

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Clash.Crypto.Calculator
  ( TestRoutines(..)
  , TestIP(..)
  , goldenRoutine
  ) where

import Clash.Prelude hiding (Mod)
import Clash.Class.Counter (Counter(..))
import Data.Type.Ord (Compare)

import Clash.Crypto.Calculator.ISA
import Clash.Crypto.Calculator.Modulo

import Test.Clash.Crypto.Calculator.InverseModulo (invMod)

goldenRoutine ∷ Mod SecP256ModPrime → Mod SecP256ModPrime → Mod SecP256ModPrime
goldenRoutine a b =
  let
    c = sq $ sq a                        -- RUN 2 Routine0
    d = tb c 0 * tb c 1                  -- RUN 1 Routine1
    e = b + d                            -- ADD
    r = tb (invMod (2 * (a + e)) - 1) 20 -- RUN 1 Arithmetic
  in
    r
 where
  sq x = x * x
  tb x y = if testBit x y then 1 else 0

data TestRoutines
  = Main
  | Routine0
  | Routine1
  | Arithmetic
  deriving (Generic, NFDataX, BitPack, Show, Ord, Eq)

type instance Compare (a ∷ TestRoutines) (b ∷ TestRoutines) =
  Compare (RoutineIndex a) (RoutineIndex b)
type RoutineIndex ∷ TestRoutines → Nat
type family RoutineIndex r = n | n → r
 where
  RoutineIndex Main       = 0
  RoutineIndex Routine0   = 1
  RoutineIndex Routine1   = 2
  RoutineIndex Arithmetic = 3

instance KnownRoutine Main where
  routine _ = Main
  knownRoutine = RoutineFacts
  type Instructions Main = -- a b
    '[ CUP 0               -- a b b
     , CUP 2               -- a b b a
     , RUN 2 Routine0      -- a b b c
     , RUN 1 Routine1      -- a b b d
     , RUN 0 Routine0      -- a b b d
     , SWP 1               -- a b d b
     , POP 1               -- a b d
     , ADD SecP256ModPrime -- a e
     , RUN 1 Arithmetic    -- r
     ]

instance KnownRoutine Routine0 where
  routine _ = Routine0
  knownRoutine = RoutineFacts
  type Instructions Routine0 =
    '[ CUP 0
     , MUL SecP256ModPrime
     ]

instance KnownRoutine Routine1 where
  routine _ = Routine1
  knownRoutine = RoutineFacts
  type Instructions Routine1 =
    '[ CUP 0
     , PUT 0
     , BIT SecP256ModPrime
     , SWP 1
     , PUT 1
     , BIT SecP256ModPrime
     , MUL SecP256ModPrime
     ]

instance KnownRoutine Arithmetic where
  routine _ = Arithmetic
  knownRoutine = RoutineFacts
  type Instructions Arithmetic =
    '[ ADD SecP256ModPrime
     , PUT 2
     , MUL SecP256ModPrime
     , PUT 0
     , INV SecP256ModPrime
     , PUT 1
     , SUB SecP256ModPrime
     , PUT 20
     , BIT SecP256ModPrime
     ]

data TestIP
  = IPMain       (RIndex Main Main)
  | IPRoutine0   (RIndex Main Routine0)
  | IPRoutine1   (RIndex Main Routine1)
  | IPArithmetic (RIndex Main Arithmetic)
  | EndOfSequence
  deriving (Generic, NFDataX, Show)

instance InstructionPointer Main TestIP where
  inc _ = \case
    IPMain n       | (False, m) ← countSuccOverflow n → IPMain m
    IPRoutine0 n   | (False, m) ← countSuccOverflow n → IPRoutine0 m
    IPRoutine1 n   | (False, m) ← countSuccOverflow n → IPRoutine1 m
    IPArithmetic n | (False, m) ← countSuccOverflow n → IPArithmetic m
    _ → EndOfSequence

  start _ = \case
    Main
      | USucc{} ← toUNat (SNat @(InstructionCount Main))
      → IPMain . RIndex 0
    Routine0
      | USucc{} ← toUNat (SNat @(InstructionCount Routine0))
      → IPRoutine0 . RIndex 0
    Routine1
      | USucc{} ← toUNat (SNat @(InstructionCount Routine1))
      → IPRoutine1 . RIndex 0
    Arithmetic
      | USucc{} ← toUNat (SNat @(InstructionCount Arithmetic))
      → IPArithmetic . RIndex 0

  instr @a _ = \case
    IPMain RIndex{..}
      | RoutineFacts ← knownRoutine @_ @Main @a
      → pure $ instructions Main Main !! iptr
    IPRoutine0 RIndex{..}
      | RoutineFacts ← knownRoutine @_ @Routine0 @a
      → pure $ instructions Main Routine0 !! iptr
    IPRoutine1 RIndex{..}
      | RoutineFacts ← knownRoutine @_ @Routine1 @a
      → pure $ instructions Main Routine1 !! iptr
    IPArithmetic RIndex{..}
      | RoutineFacts ← knownRoutine @_ @Arithmetic @a
      → pure $ instructions Main Arithmetic !! iptr
    _ → Nothing
