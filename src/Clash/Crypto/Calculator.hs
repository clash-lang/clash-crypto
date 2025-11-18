{-# LANGUAGE RecordWildCards #-}

module Clash.Crypto.Calculator where

import Clash.Prelude hiding (Mod)

import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Calculator.ISA
import Clash.Crypto.Calculator.CLU
import Clash.Crypto.ECDSA.Modulo
import Clash.Signal.Channel
import Clash.Sized.Stack

calculator ∷
  ∀ {group}
    (dom ∷ Domain). HiddenClockResetEnable dom ⇒
  ∀ (main ∷ group) → KnownRoutine main ⇒
  ∀ (ptr ∷ Type)  → (InstructionPointer main ptr, NFDataX ptr) ⇒
  ∀ stages → KnownNat stages ⇒
  ∀ regs → KnownNat regs ⇒
  (1 ≤ ArgCount main, 1 ≤ ResultCount main) ⇒
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
              ( Execute (start main sr k) None None
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

data State routine ptr a
  = WaitForInput
  | PushArgs (Index (ArgCount routine))
  | Execute ptr (Content a) (Content a)
  | PopResult Bool (Vec (ResultCount routine) a)
  deriving (Generic)

deriving instance
  ∀ routine ptr a.
  (NFDataX a, NFDataX ptr, KnownResultCount routine) ⇒
  NFDataX (State routine ptr a)

data MealyInput routine ptr a = MealyInput
  { calculatorInput ∷ Content (Vec (ArgCount routine) a)
  , cluResponse ∷ Content a
  , dataStackTop ∷ Maybe a
  , iptrStackTop ∷ Maybe ptr
  }

data MealyOutput routine ptr a = MealyOutput
  { calculatorOutput ∷ Content (Vec (ResultCount routine) a)
  , cluAction ∷ Content (ECPrime, (CluInstruction, (a, a)))
  , dataStackAction ∷ StackAction (RequiredStackSize routine) a
    -- | the sub-routine count offers a sound upper bound for the stack
    -- size here, as any routine can be pushed at most once and we
    -- cannot use recursive calls
  , iptrStackAction ∷ StackAction (SubRoutineCount routine) ptr
  }