{-|
Module      : Test.Clash.Crypto.Calculator
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Calculator'.
-}

{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Clash.Crypto.Calculator where

import Clash.Prelude hiding (Mod)
import Clash.Class.Counter (Counter(..))
import Clash.Hedgehog.Sized.Index (genIndex)
import Clash.Signal.Channel
import Language.Haskell.Unicode (type (≤))

import Data.Maybe (fromMaybe)
import Data.Monoid (First(..))
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog
import Data.Type.Ord (Compare)

import qualified Data.List as List
import qualified Data.Modular as Modular
import qualified Hedgehog.Range as Range

import Clash.Crypto.Calculator
import Clash.Crypto.Calculator.ISA
import Clash.Crypto.ECDSA.Modulo

tastyTests ∷ TestTree
tastyTests = testGroup "Clash.Crypto.Calculator"
  [ testGroup "Calculator Tests"
      [ localOption (HedgehogTestLimit (Just 10))
      $ testProperty "CLU Arithmetic" $ property $ do
          a ∷ CMod SecP256Mod ← genMod
          b ∷ CMod SecP256Mod ← genMod
          testCalculator Arithmetic ArithmeticIP a b
            $ if testBit (invGolden (2 * (a + b)) - 1) 20 then 1 else 0
      , testProperty "Routine Calls" $ property $ do
          a ∷ CMod SecP256Mod ← genMod
          testCalculator Main CallIP a 0
            $ let sq x = x * x
                  r0 = sq $ sq a
                  b0 = if testBit r0 0 then 1 else 0
                  b1 = if testBit r0 1 then 1 else 0
               in b0 * b1
      ]
  ]
 where
  genMod ∷ ∀ p m. (Monad m, KnownNat p, 3 ≤ p) ⇒ PropertyT m (Mod p)
  genMod = do
    x ← forAll $ genIndex @p $ Range.linear minBound maxBound
    return $ createMod @p x

testCalculator ∷
  ∀ (m ∷ Type → Type). Monad m ⇒
  ∀ {group}.
  ∀ (main ∷ group) → KnownRoutine main ⇒
  ∀ (ptr ∷ Type) → (InstructionPointer main ptr, NFDataX ptr) ⇒
  (ArgCount main ~ 2, ResultCount main ~ 1) ⇒
  CMod SecP256Mod →
  CMod SecP256Mod →
  CMod SecP256Mod →
  PropertyT m ()
testCalculator main ip a b c
  = (c ===)
  $ head
  $ fromMaybe (error "The returned list was empty.")
  $ getFirst
  $ foldMap First
  $ sampleN @System 1000000
  $ withClockResetEnable clockGen resetGen enableGen
  $ newsfeed
  $ calculator main ip 4 36
  $ channel
  $ fmap (a :> b :> Nil, )
  $ fromList
  $ Keep : Keep : Release : List.repeat Keep

type Q = CPrime SecP256Mod

data ArithmeticTestRoutine = Arithmetic
  deriving (Generic, NFDataX, BitPack, Show, Ord, Eq)

type instance Compare (a ∷ ArithmeticTestRoutine) b = EQ

instance KnownRoutine Arithmetic where
  routine _ = Arithmetic
  knownRoutine = RoutineFacts
  type Instructions Arithmetic =
    '[ ADD Q
     , PUT 2
     , MUL Q
     , PUT 0
     , INV Q
     , PUT 1
     , SUB Q
     , PUT 20
     , BIT Q
     ]

data ArithmeticIP = AIPEOS | AIP (RIndex Arithmetic Arithmetic)
  deriving (Generic, NFDataX)

instance InstructionPointer Arithmetic ArithmeticIP where
  inc _ = \case
    AIP n | (False, m) ← countSuccOverflow n → AIP m
    _ → AIPEOS

  start _ = \case
    Arithmetic
      | USucc{} ← toUNat (SNat @(InstructionCount Arithmetic))
      → AIP . RIndex 0

  instr @a _ = \case
    AIP RIndex{..}
      | RoutineFacts ← knownRoutine @_ @Arithmetic @a
      → pure $ instructions Arithmetic Arithmetic !! iptr
    _ → Nothing

data CallTestRoutines
  = Main
  | Routine0
  | Routine1
  deriving (Generic, NFDataX, BitPack, Show, Ord, Eq)

type instance Compare (a ∷ CallTestRoutines) (b ∷ CallTestRoutines) =
  Compare (RoutineIndex a) (RoutineIndex b)
type RoutineIndex ∷ CallTestRoutines → Nat
type family RoutineIndex r = n | n → r
 where
  RoutineIndex Main     = 0
  RoutineIndex Routine0 = 1
  RoutineIndex Routine1 = 2

instance KnownRoutine Main where
  routine _ = Main
  knownRoutine = RoutineFacts
  type Instructions Main =
    '[ POP 1
     , RUN 2 Routine0
     , RUN 1 Routine1
     , RUN 0 Routine0
     ]

instance KnownRoutine Routine0 where
  routine _ = Routine0
  knownRoutine = RoutineFacts
  type Instructions Routine0 =
    '[ CUP 0
     , MUL Q
     ]

instance KnownRoutine Routine1 where
  routine _ = Routine1
  knownRoutine = RoutineFacts
  type Instructions Routine1 =
    '[ CUP 0
     , PUT 0
     , BIT Q
     , SWP 1
     , PUT 1
     , BIT Q
     , MUL Q
     ]

data CallIP
  = CIPEOS
  | CIPMain (RIndex Main Main)
  | CIPRoutine0 (RIndex Main Routine0)
  | CIPRoutine1 (RIndex Main Routine1)
  deriving (Generic, NFDataX, Show)

instance InstructionPointer Main CallIP where
  inc _ = \case
    CIPMain n     | (False, m) ← countSuccOverflow n → CIPMain m
    CIPRoutine0 n | (False, m) ← countSuccOverflow n → CIPRoutine0 m
    CIPRoutine1 n | (False, m) ← countSuccOverflow n → CIPRoutine1 m
    _ → CIPEOS

  start _ = \case
    Main
      | USucc{} ← toUNat (SNat @(InstructionCount Main))
      → CIPMain . RIndex 0
    Routine0
      | USucc{} ← toUNat (SNat @(InstructionCount Routine0))
      → CIPRoutine0 . RIndex 0
    Routine1
      | USucc{} ← toUNat (SNat @(InstructionCount Routine1))
      → CIPRoutine1 . RIndex 0

  instr @a _ = \case
    CIPMain RIndex{..}
      | RoutineFacts ← knownRoutine @_ @Main @a
      → pure $ instructions Main Main !! iptr
    CIPRoutine0 RIndex{..}
      | RoutineFacts ← knownRoutine @_ @Routine0 @a
      → pure $ instructions Main Routine0 !! iptr
    CIPRoutine1 RIndex{..}
      | RoutineFacts ← knownRoutine @_ @Routine1 @a
      → pure $ instructions Main Routine1 !! iptr
    _ → Nothing

invGolden ∷ ∀ p. Modular.Modulus p ⇒ Mod p → Mod p
invGolden 0 = 0
invGolden x
  = fromInteger
  $ Modular.unMod
  $ fromMaybe moduloError
  $ Modular.inv
  $ Modular.toMod @p
  $ toInteger x
 where
  moduloError =
    error "The inverse always exists in a prime field."
