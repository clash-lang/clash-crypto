{-|
Module      : Clash.Signal.DataStream
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

A 'DataStream' is a 'Signal' over 'Frame's and allows the transfer of
data messages over multiple cycles. We use the term "message" to
denote a well-defined unit of data that can be separated into multiple
data pieces ("chunks") and the term "frame" to denote the data that is
sent per cycle. A frame not necessarily needs to hold any data of the
message. Hence, the interface also supports data to be transferred
non-contiguously over time.

Whenever no message is transferred, then a data stream shall ship an
'Idle' frame. A message transfer is initiated with a single 'Start'
frame, followed by an arbitrary number of 'Middle' frames, and finally
terminated by a single 'End' frame. All of these three frame types
hold exactly one data chunk. In addition to that, any number of
'Stretch' frames can appear between a 'Start' and the later 'End'
frame, which enables the possibility of non-contiguous data
transfers. The use of the special purpose 'Stretch' frame during a
message transfer makes it easy to observe that a transfer is currently
in progress although no data is available at the given cycle. If a
message fits into a single frame, then only a single 'End' frame is
used to transfer the whole message, i.e., no 'Start' frame needs to
appear before. The 'Start' and 'End' frames also can hold some
additional information, that may be useful for an application to
reassemble the message at the receiving side.
-}

{-# LANGUAGE Safe #-}

module Clash.Signal.DataStream
  ( DataStream
  , Frame(..)
  , isIdleFrame
  , isStretchFrame
  , isDataFrame
  , isStartFrame
  , isMiddleFrame
  , isEndFrame
  , mayD
  , regMayD
  , fromFrame
  , mapStart
  , mapEnd
  ) where

import Clash.Class.BitPack (BitPack)
import Control.Applicative (Applicative(..), (<$>))
import Prelude (($), id)
import Clash.Signal (Signal, HiddenClockResetEnable, register)
import Clash.XException (NFDataX, ShowX)
import Data.Bool (Bool(..))
import Data.Eq (Eq)
import Data.Functor (Functor(..))
import Data.Maybe (Maybe(..))
import Data.Ord (Ord)
import GHC.Generics (Generic)
import GHC.Records (HasField(..))
import GHC.Show (Show)

-- | A frame, as it is transferred at every cycle.
data Frame s e a where
  -- | 'Idle' frames indicate that there currently is no message
  -- being transferred.
  Idle ∷ Frame s e a
  -- | 'Stretch' frames indicate an in-progress message transfer,
  -- but with no data currently available.
  Stretch ∷ Frame s e a
  -- | 'Start' frames initiate a message transfer. They hold the first
  -- data chunk of the message and some additional data (if useful for
  -- the application). Choose @s@ to be an empty data type, if not
  -- required.
  Start ∷ s → a → Frame s e a
  -- | 'Middle' frames hold intermediate data chunks of a message.
  Middle ∷ a → Frame s e a
  -- | 'End' frames terminate a message transfer. They hold the final
  -- data chunk of the message and some additional data (if useful for
  -- the application). Choose @e@ to be an empty data type, if not
  -- required.
  End ∷ e → a → Frame s e a
  deriving (Show, Eq, Ord, Generic, NFDataX, BitPack, ShowX)

instance Functor (Frame s e) where
  fmap f = \case
    Idle      → Idle
    Stretch   → Stretch
    Start s a → Start s $ f a
    Middle  a → Middle  $ f a
    End   e a → End   e $ f a

-- | A data stream is a 'Signal' of 'Frame's.
type DataStream dom s e a = Signal dom (Frame s e a)

-- | Checks whether the given frame is an 'Idle' frame.
isIdleFrame ∷ Frame s e a → Bool
isIdleFrame = \case
  Idle → True
  _    → False

instance HasField "isIdleFrame" (Frame s e a) Bool where
  getField = isIdleFrame

instance HasField "atIdleFrame" (Frame s e a) Bool where
  getField = isIdleFrame

-- | Checks whether the given frame is a 'Stretch' frame.
isStretchFrame ∷ Frame s e a → Bool
isStretchFrame = \case
  Stretch → True
  _       → False

instance HasField "isStretchFrame" (Frame s e a) Bool where
  getField = isStretchFrame

instance HasField "atStretchFrame" (Frame s e a) Bool where
  getField = isStretchFrame

-- | Checks whether the given frame contains any message data.
isDataFrame ∷ Frame s e a → Bool
isDataFrame = \case
  Idle    → False
  Stretch → False
  _       → True

instance HasField "isDataFrame" (Frame s e a) Bool where
  getField = isDataFrame

instance HasField "hasData" (Frame s e a) Bool where
  getField = isDataFrame

-- | Checks whether the given frame is a 'Start' frame.
isStartFrame ∷ Frame s e a → Bool
isStartFrame = \case
  Start{} → True
  _       → False

instance HasField "isStartFrame" (Frame s e a) Bool where
  getField = isStartFrame

instance HasField "atStartFrame" (Frame s e a) Bool where
  getField = isStartFrame

-- | Checks whether the given frame is a 'Middle' frame.
isMiddleFrame ∷ Frame s e a → Bool
isMiddleFrame = \case
  Middle{} → True
  _        → False

instance HasField "isMiddleFrame" (Frame s e a) Bool where
  getField = isMiddleFrame

instance HasField "atMiddleFrame" (Frame s e a) Bool where
  getField = isMiddleFrame

-- | Checks whether the given frame is an 'End' frame.
isEndFrame ∷ Frame s e a → Bool
isEndFrame = \case
  End{} → True
  _     → False

instance HasField "isEndFrame" (Frame s e a) Bool where
  getField = isEndFrame

instance HasField "atEndFrame" (Frame s e a) Bool where
  getField = isEndFrame

-- | Replaces frames holding no data with the first argument and
-- extracts the data from the frame otherwise and modifies it using
-- the second argument.
--
-- The function works similar to 'Data.Maybe.maybe' for the
-- 'Data.Maybe.Maybe' type, which is also the reason for its
-- particular name.
mayD ∷ b → (a → b) → Frame s e a → b
mayD x f = \case
  Idle      → x
  Stretch   → x
  Start _ a → f a
  Middle  a → f a
  End   _ a → f a

-- | A version of 'register' that only updates its content when its
-- second argument is a frame holding some message chunk.
--
-- The function works similar to 'Clash.Signal.regMaybe' for the
-- 'Data.Maybe.Maybe' type, which is also the reason for it's
-- particular name.
regMayD ∷
  (HiddenClockResetEnable dom, NFDataX a) ⇒
  a → Signal dom (Frame s e a) → Signal dom a
regMayD i s = r
  where
   r = register i $ (`mayD` id) <$> r <*> s

-- | Extract the data chunk when given a data frame, otherwise return
-- 'Nothing'.
fromFrame :: Frame s e a -> Maybe a
fromFrame = mayD Nothing Just

-- | Maps the provided function only over the additional data shipped
-- with the 'Start' frames.
mapStart ∷ (b → c) → DataStream dom b e a → DataStream dom c e a
mapStart f = (<$>) $ \case
  Idle      → Idle
  Stretch   → Stretch
  Start s x → Start (f s) x
  Middle x  → Middle x
  End e x   → End e x

-- | Maps the provided function only over the additional data shipped
-- with the 'End' frames.
mapEnd ∷ (b → c) → DataStream dom s b a → DataStream dom s c a
mapEnd f = (<$>) $ \case
  Idle      → Idle
  Stretch   → Stretch
  Start s x → Start s x
  Middle x  → Middle x
  End e x   → End (f e) x
