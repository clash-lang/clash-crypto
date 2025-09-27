{-|
Module      : Clash.Signal.DataStream
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

A 'DataStream' is a 'Signal' over 'Frame's, which allows to transfer
data messages over multiple cycles, where we use the term "message" to
denote a well-defined unit of data that can be separated into multiple
data pieces ("chunks"), while the term "frame" denotes the data that
is sent per cycle. Hence, a frame not necessarily needs to hold some
data of the message. In that regard, the interface also supports data
to be transferred non-contiguously over time.

Every data stream ships an 'Idle' frame, whenever no message gets
transferred, while the transfer of a message is initiated via a single
'Start' frame, followed by an arbitrary number of 'Middle' frames,
finally ending with a single 'End' frame, where every of these three
frame types holds a single data chunk. In addition to that, any number
of 'NoData' frames can appear between a 'Start' the next later 'End'
frame, which enables the possibility of non-contiguous data
transfer. The use of the special purpose 'NoData' frame during a
message transfer makes it easy to observe that the transfer is
currently in progress although no data is currently available. If a
message fits into a single frame, then only a single 'End' frame is
used to transfer the whole message, i.e., no 'Start' frame needs
appear before. The 'Start' and 'End' frames also can hold some
additional data, that may be useful for the particular application for
reassembling the message.
-}

{-# LANGUAGE NoTemplateHaskell #-}
{-# LANGUAGE NoGeneralizedNewtypeDeriving #-}
{-# LANGUAGE Safe #-}

module Clash.Signal.DataStream
  ( DataStream
  , Frame(..)
  , isDataFrame
  , isStartFrame
  , isMiddleFrame
  , isEndFrame
  , mayD
  , regMayD
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
import Data.Ord (Ord)
import GHC.Generics (Generic)
import GHC.Records (HasField(..))
import GHC.Show (Show)

-- | A frame, as it is transferred with every cycle.
data Frame s e a where
  -- | The 'Idle' frame indicates that there is currently no message
  -- being transferred.
  Idle ∷ Frame s e a
  -- | The 'NoData' frame indicates that a message transfer is
  -- currently in progress, but no data is currently available.
  NoData ∷ Frame s e a
  -- | The 'Start' frame initiates the transfer of a new message. It
  -- holds the first data chunk of the message and some additional data
  -- (if useful for the application). Choose @s@ to be an empty data
  -- type, if not required.
  Start  ∷ s → a → Frame s e a
  -- | The 'Middle' frame holds some intermediate data chunk of the
  -- message.
  Middle ∷ a → Frame s e a
  -- | The 'End' frame completes the transfer of a message. It hold
  -- the final data chunk of the message and some additional data (if
  -- useful for the application). Choose @e@ to be an empty data type,
  -- if not required.
  End ∷ e → a → Frame s e a
  deriving (Show, Eq, Ord, Generic, NFDataX, BitPack, ShowX)

instance Functor (Frame s e) where
  fmap f = \case
    Idle      → Idle
    NoData    → NoData
    Start s a → Start s $ f a
    Middle  a → Middle  $ f a
    End   e a → End   e $ f a

-- | A data stream is a 'Signal' of 'Frame's.
type DataStream dom s e a = Signal dom (Frame s e a)

-- | Checks whether the given frame contains any message data.
isDataFrame ∷ Frame s e a → Bool
isDataFrame = \case
  Idle   → False
  NoData → False
  _      → True

instance HasField "isDataFrame" (Frame s e a) Bool where
  getField = isDataFrame

instance HasField "hasData" (DataStream dom s e a) (Signal dom Bool) where
  getField = fmap isDataFrame

-- | Checks whether the given frame is a 'Start' frame.
isStartFrame ∷ Frame s e a → Bool
isStartFrame = \case
  Start{} → True
  _       → False

instance HasField "isStartFrame" (Frame s e a) Bool where
  getField = isStartFrame

instance HasField "atStartFrame" (DataStream dom s e a) (Signal dom Bool) where
  getField = fmap isStartFrame

-- | Checks whether the given frame is a 'Middle' frame.
isMiddleFrame ∷ Frame s e a → Bool
isMiddleFrame = \case
  Middle{} → True
  _        → False

instance HasField "isMiddleFrame" (Frame s e a) Bool where
  getField = isMiddleFrame

instance HasField "atMiddleFrame" (DataStream dom s e a) (Signal dom Bool) where
  getField = fmap isMiddleFrame

-- | Checks whether the given frame is an 'End' frame.
isEndFrame ∷ Frame s e a → Bool
isEndFrame = \case
  End{} → True
  _     → False

instance HasField "isEndFrame" (Frame s e a) Bool where
  getField = isEndFrame

instance HasField "atEndFrame" (DataStream dom s e a) (Signal dom Bool) where
  getField = fmap isEndFrame

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
  NoData    → x
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

-- | Maps the provided function only over the additional data shipped
-- with the 'Start' frames.
mapStart ∷ (b → c) → DataStream dom b e a → DataStream dom c e a
mapStart f = (<$>) $ \case
  Idle      → Idle
  NoData    → NoData
  Start s x → Start (f s) x
  Middle x  → Middle x
  End e x   → End e x

-- | Maps the provided function only over the additional data shipped
-- with the 'End' frames.
mapEnd ∷ (b → c) → DataStream dom s b a → DataStream dom s c a
mapEnd f = (<$>) $ \case
  Idle      → Idle
  NoData    → NoData
  Start s x → Start s x
  Middle x  → Middle x
  End e x   → End (f e) x
