{-|
Module      : Clash.Signal.Channel
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

A 'Channel' is a special purpose 'Signal' additionally keeping track
of the availability and temporally stability of the data it
captures. On the one hand, a channel makes it more comfortable for the
data provider to release and maintain the provided data over time. On
the other hand, it helps the consumer to access the data and keep
track of the temporal changes.
-}

{-# LANGUAGE NoTemplateHaskell #-}
{-# LANGUAGE NoGeneralizedNewtypeDeriving #-}
{-# LANGUAGE Safe #-}

module Clash.Signal.Channel
  ( -- * Channel type
    Channel
    -- * Construction
  , ProviderAction(..)
  , channel
  , cachedChannel
    -- * Accessors
  , content
  , hasUpdates
  , newsfeed
  , isEmpty
  , isNonEmpty
  , contentFilter
  , channelGuard
  ) where

import Clash.Class.BitPack (BitPack)
import Clash.Prelude.Mealy (mealy)
import Clash.Signal (Signal, HiddenClockResetEnable)
import Clash.Signal.Bundle (Bundle(..))
import Clash.XException (NFDataX(..), ShowX)
import Control.Applicative (Applicative(..), Alternative(..), (<$>))
import Data.Bool (Bool(..))
import Data.Eq (Eq)
import Data.Enum (Enum, Bounded)
import Data.Function (($), (.))
import Data.Functor (Functor(..), (<&>))
import Data.Foldable (Foldable(..))
import Data.Maybe (Maybe(..))
import Data.Monoid (Monoid(..))
import Data.Ord (Ord)
import Data.Semigroup (Semigroup(..))
import Data.Traversable (Traversable(..))
import GHC.Generics (Generic)
import GHC.Records (HasField(..))
import GHC.Show (Show)

-- | An extended option type that allows to differentiate between
-- whether some data is fresh or old.
data Content a = None | Fresh a | Old a
  deriving (Show, Eq, Ord, Generic, NFDataX, BitPack, ShowX)

instance Semigroup a ⇒ Semigroup (Content a) where
  None    <> p       = p
  p       <> None    = p
  Fresh x <> Fresh y = Fresh $ x <> y
  Fresh x <> Old y   = Fresh $ x <> y
  Old x   <> Fresh y = Fresh $ x <> y
  Old x   <> Old y   = Old $ x <> y

instance Semigroup a ⇒ Monoid (Content a) where
  mempty = None

instance Functor Content where
  fmap f = \case
    None    → None
    Fresh x → Fresh $ f x
    Old x   → Old $ f x

instance Applicative Content where
  pure = Old

  None    <*> _       = None
  _       <*> None    = None
  Fresh f <*> Fresh x = Fresh $ f x
  Fresh f <*> Old x   = Fresh $ f x
  Old f   <*> Fresh x = Fresh $ f x
  Old f   <*> Old x   = Old $ f x

instance Alternative Content where
  empty = None

  None <|> p = p
  p    <|> _ = p

-- | A channel is a signal that either holds value or none.
-- Additionally, if holding a signal, the channel keeps track of the
-- hold value being fresh, i.e., updated at the current cycle, or not.
--
-- From a theoretical point of view, a 'Channel' can be considered to
-- be a 'Signal' over a special 'Monoid' that enables some more
-- powerful instances for 'Functor', 'Applicative', 'Alternative',
-- 'Foldable' and 'Traversable'.
newtype Channel dom a = Channel
  { getContent ∷ Signal dom (Content a)
  }

instance NFDataX a ⇒ NFDataX (Channel dom a) where
  deepErrorX = Channel . deepErrorX
  hasUndefined = hasUndefined . getContent
  ensureSpine = Channel . ensureSpine . getContent
  rnfX = rnfX . getContent

instance Functor (Channel dom) where
  fmap f = Channel . fmap (fmap f) . getContent

instance Applicative (Channel dom) where
  pure = Channel . pure . pure
  Channel f <*> Channel x = Channel $ fmap (<*>) f <*> x

instance Alternative (Channel dom) where
  empty = Channel $ pure empty
  Channel x <|> Channel y = Channel $ (<|>) <$> x <*> y

instance Foldable (Channel dom) where
  foldMap f = fold . fmap f

  fold (Channel c) = case fold c of
    None    → mempty
    Fresh x → x
    Old x   → x

instance Traversable (Channel dom) where
  traverse f = fmap Channel . traverse g . getContent
   where
     g = \case
       None    → pure None
       Fresh x → Fresh <$> f x
       Old x   → Old <$> f x

-- | A safe control interface for maintaining a 'Channel'.
data ProviderAction = Keep | Release | Clear
  deriving (Show, Eq, Ord, Bounded, Enum, Generic, NFDataX, BitPack, ShowX)

-- | Returns the content of the channel wrapped into a 'Maybe`.
content ∷ Channel dom a → Signal dom (Maybe a)
content c = getContent c <&> \case
  None    → Nothing
  Fresh x → Just x
  Old x   → Just x

instance HasField "content" (Channel dom a) (Signal dom (Maybe a)) where
  getField = content

-- | A Boolean flag indicating the points in time where the channel gets
-- updated.
hasUpdates ∷ Channel dom a → Signal dom Bool
hasUpdates c = getContent c <&> \case
  Fresh{} → True
  _       → False

instance HasField "hasUpdates" (Channel dom a) (Signal dom Bool) where
  getField = hasUpdates

-- | The content of a channel, but only at the points in time where it
-- is fresh.
newsfeed ∷ Channel dom a → Signal dom (Maybe a)
newsfeed c = getContent c <&> \case
  Fresh x → Just x
  _       → Nothing

instance HasField "newsfeed" (Channel dom a) (Signal dom (Maybe a)) where
  getField = newsfeed

-- | A Boolean flag indicating the points in time at which the channel
-- is empty.
isEmpty ∷ Channel dom a → Signal dom Bool
isEmpty c = getContent c <&> \case
  None → True
  _    → False

instance HasField "isEmpty" (Channel dom a) (Signal dom Bool) where
  getField = isEmpty

-- | A Boolean flag indicating the points in time at which the channel
-- holds some data.
isNonEmpty ∷ Channel dom a → Signal dom Bool
isNonEmpty c = getContent c <&> \case
  None → False
  _    → True

instance HasField "isNonEmpty" (Channel dom a) (Signal dom Bool) where
  getField = isNonEmpty

-- | Turns a 'Signal' into a 'Channel' via adding a 'ProviderAction'
-- with the assumption that the data from the input keeps stable after
-- being released until the next release or being cleared.
--
-- If the input signal cannot maintain this condition, consider using
-- 'cachedChannel' instead.
channel ∷
  HiddenClockResetEnable dom ⇒
  Signal dom a →
  Signal dom ProviderAction →
  Channel dom a
channel cnt act = Channel $ mealy (~~>) False $ bundle (cnt, act)
 where
  _    ~~> (x, Release) = (True,  Fresh x)
  True ~~> (x, Keep   ) = (True,  Old x  )
  _    ~~> _            = (False, None   )

-- | Turns a 'Signal' into a 'Channel' via adding a 'ProviderAction',
-- where data from the input is only read at points in time at which
-- the 'Release' action is selected. This particular input then is
-- latched until the provider chooses to 'Release' some other data or
-- to 'Clear' the channel.
--
-- Note that this channel constructor requires additional memory for
-- caching the input. If the input keeps stable after a 'Release'
-- anyway, then it might be desirable to use 'channel' instead.
cachedChannel ∷
  (HiddenClockResetEnable dom, NFDataX a) ⇒
  Signal dom a →
  Signal dom ProviderAction →
  Channel dom a
cachedChannel cnt act = Channel $ mealy (~~>) None $ bundle (cnt, act)
 where
  _ ~~> (_, Clear)   = (None,  None   )
  _ ~~> (x, Release) = (Old x, Fresh x)
  c ~~> (_, Keep)    = (c,     c      )

-- | Filters the content of a channel, where the filter is only
-- evaluated at the points in time where the content gets updated.
contentFilter ∷
  (HiddenClockResetEnable dom, NFDataX a) ⇒
  (a → Bool) →
  Channel dom a →
  Channel dom a
contentFilter f = Channel . mealy (~~>) True . getContent
 where
  _    ~~> c@(Fresh x) = g (f x) c
  keep ~~> c           = g keep  c

  g b c = (b, if b then c else None)

-- | Restricts channel access over time, where the content of the
-- input channel only passes the guard, if the Boolean selector
-- evaluates positively at the point in time where content gets
-- released.
channelGuard ∷
  (HiddenClockResetEnable dom, NFDataX a) ⇒
  Signal dom Bool →
  Channel dom a →
  Channel dom a
channelGuard s (Channel a) = Channel $ mealy (~~>) False $ bundle (s, a)
 where
  _     ~~> (True,  Fresh x) = (True,  Fresh x)
  _     ~~> (False, Fresh _) = (False, None   )
  True  ~~> (_,     cnt    ) = (True,  cnt    )
  False ~~> (_,     _      ) = (False, None   )
