{-|
Module      : Clash.Crypto.Calculator
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

A calculator for running a compile-time known instruction sequence.
-}

{-# LANGUAGE RecordWildCards #-}

module Clash.Crypto.Calculator
  ( calculator
  ) where

import Clash.Prelude hiding (Mod)

import Clash.Crypto.Calculator.CLU
import Clash.Crypto.Calculator.ISA
import Clash.Crypto.Calculator.Modulo
import Clash.Signal.Channel
import Clash.Sized.Stack

-- | Runs the instruction sequence referenced by the first required
-- type argument.
calculator ∷
  ∀ {group}
    (dom ∷ Domain). HiddenClockResetEnable dom ⇒
  ∀ (main ∷ group) → KnownRoutine main ⇒
  -- ^ the routine referring to the executed instruction sequence
  ∀ (ptr ∷ Type) → (InstructionPointer main ptr, NFDataX ptr) ⇒
  -- ^ the instruction pointer type that is related to the routine type
  ∀ stages → KnownNat stages ⇒
  -- ^ the staging depth of the Karatsuba based multiplier
  ∀ regs → KnownNat regs ⇒
  -- ^ the size of the base multiplier
  Channel dom (Vec (ArgCount main) (Mod (CPrime (SecP256Mod)))) →
  -- ^ initial stack content (rightmost element at the top)
  Channel dom (Vec (ResultCount main) (Mod (CPrime (SecP256Mod))))
  -- ^ final stack content (rightmost element at the top)
calculator main ptr stages regs input
  | RoutineFacts ← knownRoutine @group @main @(Mod (CPrime (SecP256Mod)))
  = let
      out = MealyOutput
        { calculatorOutput = None
        , cluAction        = None
        , dataStackAction  = Inspect 0
        , iptrStackAction  = Inspect 0
        } ∷ MealyOutput main ptr (Mod (CPrime (SecP256Mod)))

      next ip = Execute (inc main ip) None None

      m = mealy (~~>) (WaitForInput @main @ptr)
        $ MealyInput @main @ptr
            <$> getContent input
            <*> ( bitCoerce
                   <$> getContent
                         ( delayC
                         $ clu stages regs
                         $ g <$> Channel m.cluAction
                         )
                )
            <*> (fst <$> stack m.dataStackAction)
            <*> (fst <$> stack m.iptrStackAction)

      g (SecP256Mod, (op, xy)) = (op, (bitCoerce xy, natToNum @(CPrime SecP256Mod)))
      g (SecP256Ord, (op, xy)) = (op, (bitCoerce xy, natToNum @(CPrime SecP256Ord)))

      -- / wait for some input / --

      _ ~~> (calculatorInput → None)
        = (WaitForInput, out)

      WaitForInput ~~> (calculatorInput → Old{})
        = (WaitForInput, out)

      -- / push the arguments to the stack / --

      _ ~~> (calculatorInput → Fresh{})
        = ( PushArgs 0
          ,  out { dataStackAction = Pop maxBound
                 , iptrStackAction = Pop maxBound
                 }
          )

      PushArgs n ~~> (calculatorInput → Old v)
        = ( if n < maxBound
            then PushArgs $ n + 1
            else Execute (start main (routine main) 0) None None
          , out { dataStackAction = Push $ v !! n }
          )

      -- / execute the current instruction / --

      Execute ip mx my ~~> MealyInput{..}
        | Just i ← instr main ip
        = case i of
            PUT x → (next ip, out { dataStackAction = Push x   })
            POP n → (next ip, out { dataStackAction = Pop n    })
            SWP n → (next ip, out { dataStackAction = Swap n   })
            CUP n → (next ip, out { dataStackAction = CopyUp n })
            RUN 0 _ → (next ip, out)
            RUN k sr →
              ( Execute (start main sr $ k - 1) None None
              , out { iptrStackAction = Push ip }
              )
            -- store the first argument
            CLU p op → case my of
              None →
                ( Execute ip None (maybe None Fresh dataStackTop)
                , out { dataStackAction = Pop 1 }
                )
              _ | y ← case my of { Old y → y ; Fresh y → y } → case mx of
                -- store the second argument
                None →
                  ( Execute ip (maybe None Fresh dataStackTop) my
                  , out { dataStackAction = Pop 1 }
                  )
                _ | x ← case mx of { Old x → x ; Fresh x → x } →
                  case cluResponse of
                    Fresh z → (next ip, out { dataStackAction = Push z })
                    _       →
                      ( Execute ip (Old x) (Old y)
                      , out { cluAction = (p, ) . (op, ) <$> (liftA2 (,) mx my) }
                      )

      -- / end of instruction sequence / --

      Execute{} ~~> (iptrStackTop → Just ip)
        = (next ip, out { iptrStackAction = Pop 1 })

      Execute{} ~~> (dataStackTop → Just x)
        = ( PopResult True $ x +>> repeat 0
          , out { dataStackAction = Pop 1 }
          )

      Execute{} ~~> _
        = ( PopResult True $ repeat 0
          , out { calculatorOutput = Fresh $ repeat 0 }
          )

      PopResult _ v ~~> (dataStackTop → Just x)
        = ( PopResult True $ x +>> v
          , out { dataStackAction = Pop 1 }
          )

      PopResult b v ~~> _
        = ( PopResult False v
          , out { calculatorOutput = if b then Fresh v else Old v }
          )
    in
      Channel m.calculatorOutput

-- | Internal state of the calculator's Mealy machine.
data State routine ptr a
  = -- | wait for the input arguments
    WaitForInput
  | -- | push the arguments to the stack
    PushArgs (Index (ArgCount routine))
  | -- | run the sequence
    Execute ptr (Content a) (Content a)
  | -- | pop the result from the stack
    PopResult Bool (Vec (ResultCount routine) a)
  deriving (Generic)

deriving instance
  ∀ routine ptr a.
  (NFDataX a, NFDataX ptr, KnownResultCount routine) ⇒
  NFDataX (State routine ptr a)

-- | The input to the calculator's Mealy machine.
data MealyInput routine ptr a = MealyInput
  { -- | the input to the calculator
    calculatorInput ∷ Content (Vec (ArgCount routine) a)
  , -- | the output of the CLU
    cluResponse ∷ Content a
  , -- | the output of the data stack
    dataStackTop ∷ Maybe a
  , -- | the output of the instruction pointer stack
    iptrStackTop ∷ Maybe ptr
  }

-- | The output of the calculator's Mealy machine.
data MealyOutput routine ptr a = MealyOutput
  { -- | the output of the calculator
    calculatorOutput ∷ Content (Vec (ResultCount routine) a)
  , -- | the input to the CLU
    cluAction ∷ Content (ECPrime, (CluInstruction, (a, a)))
  , -- | the input to the data stack
    dataStackAction ∷ StackAction (RequiredStackSize routine) a
    -- | the input to the instruction pointer stack
    --
    -- Note that the subroutine count is a sound upper bound for the
    -- stack size, as any routine can be pushed at most once and we
    -- do not allow recursive calls.
  , iptrStackAction ∷ StackAction (SubRoutineCount routine) ptr
  }
