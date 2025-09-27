{-|
Module      : Clash.Signal.Channel
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

A 'Channel' is a special purpose 'Signal' additionally keeping track
of the availability and temporal stability of the data it
captures. On the one hand, a channel makes it more comfortable for the
data provider to release and maintain the provided data over time. On
the other hand, it helps the consumer to access the data and keep
track of the temporal changes.
-}

{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NoTemplateHaskell #-}
{-# LANGUAGE NoGeneralizedNewtypeDeriving #-}
{-# LANGUAGE Safe #-}

module Clash.Signal.Channel
  ( -- * Channel Type
    Channel
    -- * Construction
  , ProviderAction(..)
  , channel
  , cachedChannel
  , cachedFromMaybe
    -- * Accessors
  , content
  , hasUpdates
  , newsfeed
  , isEmpty
  , isNonEmpty
    -- * Transformers
  , keep
  , keepD
  , delayC
  , enhance
  , CompMode
  , pattern Computing
  , pattern Releasing
    -- * Combinators
  , join
  , disjoin
  , filterC
  , guardC
  , muxC
  , zipC
  , unzipC
  , zipWithC
  , zipRecent
  ) where

import Clash.Prelude.Safe hiding (fold, unzip)

import Data.Foldable (Foldable(..))
import Data.Functor ((<&>), unzip)
import GHC.Records (HasField(..))

-- | An extended option type that allows to differentiate between
-- old and fresh data.
data Content a = None | Fresh a | Old a
  deriving
    ( Show, Eq, Ord, Generic, NFDataX, BitPack, ShowX
    , Functor, Traversable
    )

instance Semigroup a ⇒ Semigroup (Content a) where
  None    <> p       = p
  p       <> None    = p
  Fresh x <> Fresh y = Fresh $ x <> y
  Fresh x <> Old y   = Fresh $ x <> y
  Old x   <> Fresh y = Fresh $ x <> y
  Old x   <> Old y   = Old $ x <> y

instance Semigroup a ⇒ Monoid (Content a) where
  mempty = None

instance Foldable Content where
  foldMap f = \case
    Fresh a → f a
    _       → mempty

  foldr f z = \case
    Fresh x → f x z
    _       → z

  foldl f z = \case
    Fresh x → f z x
    _       → z

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

  None    <|> p       = p
  p       <|> None    = p
  Fresh x <|> _       = Fresh x
  _       <|> Fresh x = Fresh x
  Old x   <|> _       = Old x

-- | A channel is a signal that either holds a value or none.
-- Additionally, if holding a value, the channel keeps track of the
-- held value being fresh, i.e., updated at the current cycle, or not.
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
  -- | Always selects the channel with the most recent release.
  Channel x <|> Channel y = Channel $ (<|>) <$> x <*> y

instance Foldable (Channel dom) where
  foldMap f = fold . fmap f
  fold = fold . fmap fold . getContent

instance Traversable (Channel dom) where
  traverse f = fmap Channel . traverse (traverse f) . getContent

-- | A safe control interface for maintaining a 'Channel'.
data ProviderAction = Keep | Release | Clear
  deriving (Show, Eq, Ord, Bounded, Enum, Generic, NFDataX, BitPack, ShowX)

-- | Returns the content of the channel wrapped into a 'Maybe`.
content ∷ ∀ a dom. Channel dom a → Signal dom (Maybe a)
content c = getContent c <&> \case
  None    → Nothing
  Fresh x → Just x
  Old x   → Just x

instance HasField "content" (Channel dom a) (Signal dom (Maybe a)) where
  getField = content

-- | A Boolean flag indicating the points in time where the channel gets
-- updated.
hasUpdates ∷ ∀ a dom. Channel dom a → Signal dom Bool
hasUpdates c = getContent c <&> \case
  Fresh{} → True
  _       → False

instance HasField "hasUpdates" (Channel dom a) (Signal dom Bool) where
  getField = hasUpdates

-- | The content of a channel, but only at the points in time where it
-- is fresh.
newsfeed ∷ ∀ a dom. Channel dom a → Signal dom (Maybe a)
newsfeed c = getContent c <&> \case
  Fresh x → Just x
  _       → Nothing

instance HasField "newsfeed" (Channel dom a) (Signal dom (Maybe a)) where
  getField = newsfeed

-- | A Boolean flag indicating the points in time at which the channel
-- is empty.
isEmpty ∷ ∀ a dom. Channel dom a → Signal dom Bool
isEmpty c = getContent c <&> \case
  None → True
  _    → False

instance HasField "isEmpty" (Channel dom a) (Signal dom Bool) where
  getField = isEmpty

-- | A Boolean flag indicating the points in time at which the channel
-- holds some data.
isNonEmpty ∷ ∀ a dom. Channel dom a → Signal dom Bool
isNonEmpty = fmap not . isEmpty

instance HasField "isNonEmpty" (Channel dom a) (Signal dom Bool) where
  getField = isNonEmpty

-- | Turns a 'Signal' into a 'Channel' via adding a 'ProviderAction'
-- with the assumption that the data from the input stays stable after
-- being released until being cleared or released again.
--
-- If the input signal cannot maintain this condition, consider using
-- 'cachedChannel' instead.
channel ∷
  ∀ a dom.
  HiddenClockResetEnable dom ⇒
  Signal dom (a, ProviderAction) →
  Channel dom a
channel = Channel . mealy (~~>) False
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
-- caching the input. If the input stays stable after a 'Release'
-- anyway, then it might be desirable to use 'channel' instead.
cachedChannel ∷
  ∀ a dom.
  (HiddenClockResetEnable dom, NFDataX a) ⇒
  Signal dom (a, ProviderAction) →
  Channel dom a
cachedChannel = Channel . mealy (~~>) None
 where
  _ ~~> (_, Clear)   = (None,  None   )
  _ ~~> (x, Release) = (Old x, Fresh x)
  c ~~> (_, Keep)    = (c,     c      )

-- | Turns a signal of 'Maybe'-wrapped values into a cached channel
-- that releases every 'Just'-wrapped input and holds it until the
-- next 'Just'-wrapped input is fed in.
cachedFromMaybe ∷
  ∀ a dom.
  (NFDataX a, HiddenClockResetEnable dom) ⇒
  Signal dom (Maybe a) →
  Channel dom a
cachedFromMaybe =
  cachedChannel . fmap (maybe (undefined, Keep) (, Release))

-- | Filters the content of a channel, where the filter is only
-- evaluated at the points in time at which the content gets updated.
filterC ∷
  ∀ a dom.
  HiddenClockResetEnable dom ⇒
  (a → Bool) →
  Channel dom a →
  Channel dom a
filterC f = Channel . mealy (~~>) True . getContent
 where
  _ ~~> c@(Fresh x) = g (f x) c
  s ~~> c           = g s c

  g b c = (b, if b then c else None)

-- | Restricts channel access over time: the content of the input
-- channel only passes the guard, if the Boolean selector evaluates to
-- @True@ at the point in time where content gets released.
guardC ∷
  ∀ a dom.
  HiddenClockResetEnable dom ⇒
  Signal dom Bool →
  Channel dom a →
  Channel dom a
guardC b (Channel s) = Channel $ mealy (~~>) False $ bundle (b, s)
 where
  _     ~~> (True,  Fresh x) = (True,  Fresh x)
  _     ~~> (False, Fresh _) = (False, None   )
  True  ~~> (_,     cnt    ) = (True,  cnt    )
  False ~~> (_,     _      ) = (False, None   )

-- | A channel specific variant of 'mux' that reads from a 'Signal' to
-- mux between the two possible alternatives.
muxC ∷ ∀ a dom. Signal dom Bool → Channel dom a → Channel dom a → Channel dom a
muxC b (Channel x) (Channel y) = Channel $ mux b x y

-- | Data with a Boolean flag indicating whether the data is final or
-- an intermediate result of a computation.
type CompMode a = (a, Bool)

-- | Data that results from some ongoing computation.
{-# COMPLETE Computing, Releasing #-}
pattern Computing ∷ a → CompMode a
pattern Computing a = (a, True)

-- | The finally computed result.
pattern Releasing ∷ a → CompMode a
pattern Releasing a = (a, False)

-- | Enhances a channel by a multi-cycle computation that starts on
-- every fresh input and may take multiple cycles before releasing a
-- result. Updates on the input channel cause delayed releases on the
-- output channel in that regard. A minimum of a one cycle delay gets
-- introduced.
enhance ∷
  ∀ a s b dom.
  (NFDataX s, HiddenClockResetEnable dom) ⇒
  -- | Sets up the initial computation state. This function is
  -- executed once for every fresh input being received.
  (a → s) →
  -- | Converts the final computation state into the released result.
  (a → s → b) →
  -- | Iterates over the input and computation state. The given
  -- transformation starts executing after a fresh input has been
  -- received and runs until a 'Releasing' state is returned.
  (a → s → CompMode s) →
  -- | The input channel.
  Channel dom a →
  -- | The enhanced output channel.
  Channel dom b
enhance put get compute =
  channel . mealy (~~>) (Releasing undefined) . getContent
 where
  _           ~~> None    = (Releasing undefined, (undefined,  Clear  ))
  _           ~~> Fresh x = (Computing $ put x  , (undefined,  Clear  ))
  Releasing s ~~> Old x   = (Releasing s        , (get x s,    Keep   ))
  Computing s ~~> Old x   = case compute x s of
    Releasing r →           (Releasing r        , (get x r,    Release))
    Computing r →           (Computing r        , (undefined,  Clear  ))

-- | Joins two channels together. The joint channel always outputs the
-- most recently released content of the two input channels. The
-- content of the channel being passed as the first argument is
-- selected if both channels are updated simultaneously.
join ∷
  ∀ a dom. HiddenClockResetEnable dom ⇒
  Channel dom a → Channel dom a → Channel dom a
join (Channel x) (Channel y) =
  Channel $ mealy (~~>) (0 ∷ Unsigned 1) $ liftA2 (,) x y
 where
  _ ~~> (Fresh x0, _       ) = (0, Fresh x0)
  _ ~~> (_       , Fresh x1) = (1, Fresh x1)
  0 ~~> (Old x0  ,   _     ) = (0, Old x0  )
  0 ~~> _                    = (0, None    )
  _ ~~> (_       , Old x1  ) = (1, Old x1  )
  _ ~~> _                    = (1, None    )

-- | Assigns some 'Either' content of the input channel to either the
-- left or right output channel, where the 'Left' and 'Right'
-- constructors determine the corresponding destination. Both output
-- channels will never hold some content at the same time.
disjoin ∷
  ∀ a b dom. HiddenClockResetEnable dom ⇒
  Channel dom (Either a b) → (Channel dom a, Channel dom b)
disjoin (Channel s) = bothC $ unbundle $ s <&> \case
  None            → (None   , None   )
  Fresh (Left x)  → (Fresh x, None   )
  Fresh (Right y) → (None   , Fresh y)
  Old   (Left x)  → (Old x  , None   )
  Old   (Right y) → (None   , Old y  )
 where
  bothC (x, y) = (Channel x, Channel y)

-- | Keeps the content of the channel until the next release.
keep ∷
  ∀ a dom. (NFDataX a, HiddenClockResetEnable dom) ⇒
  Channel dom a → Channel dom a
keep = Channel . mealy (~~>) Nothing . getContent
 where
  _ ~~> Fresh x = (Just x, Fresh x)
  s ~~> _       = (s, maybe None Old s)

-- | Keeps the content of the channel until the next release and
-- delays the output by a cycle. The operation is semantically
-- equivalent to @(keep . delayC)@, while only requiring half the
-- number of storage bits.
keepD ∷
  ∀ a dom. (NFDataX a, HiddenClockResetEnable dom) ⇒
  Channel dom a → Channel dom a
keepD = Channel . moore (~~>) id None . getContent
 where
  _       ~~> Fresh x = Fresh x
  Fresh x ~~> _       = Old x
  s       ~~> _       = s

-- | The channel equivalent of 'delay'.
delayC ∷  ∀ a dom. (NFDataX a, HiddenClock dom, HiddenEnable dom) ⇒
  Channel dom a → Channel dom a
delayC = Channel . delay None . getContent

-- | Zips two channels together, where the resulting channel releases
-- new content whenever one of the two input channels gets updated and
-- only holds content when both input channels hold content as well.
zipC ∷ ∀ a b dom. Channel dom a → Channel dom b → Channel dom (a, b)
zipC = liftA2 (,)

-- | Unzips two channels, where the releases of the resulting channels
-- align with the releases of the input.
unzipC ∷ ∀ a b dom. Channel dom (a, b) → (Channel dom a, Channel dom b)
unzipC = unzip

-- | Zips two channels together using the given coupling function. The
-- resulting channel releases new content whenever one of the two
-- input channels gets updated and only holds content when both
-- input channels hold content as well.
zipWithC ∷
  ∀ a b c dom.
  -- | coupling function
  (a → b → c) →
  -- | first channel
  Channel dom a →
  -- | second channel
  Channel dom b →
  -- | output channel
  Channel dom c
zipWithC f a b =
  uncurry f <$> zipC a b

-- | Zips the most recent content of the first input channel with the
-- content of the second one using the given coupling function. If the
-- first input channel is updated after the second one turned stable,
-- then the output channel gets cleared. Conversely, if the second
-- input channel is updated while the first one stays stable, then
-- the output channel gets updated as well.
zipRecent ∷
  ∀ a b c dom. HiddenClockResetEnable dom ⇒
  -- | coupling function
  (a → b → c) →
  -- | first channel
  Channel dom a →
  -- | second channel
  Channel dom b →
  -- | output channel
  Channel dom c
zipRecent f (Channel x) (Channel y) =
  Channel $ mealy (~~>) (0 ∷ Unsigned 1) $ bundle (x, y)
 where
  _ ~~> (None   , _      ) = (0, None         )
  _ ~~> (_      , None   ) = (0, None         )
  _ ~~> (Fresh u, Fresh v) = (1, Fresh $ f u v)
  _ ~~> (Old u  , Fresh v) = (1, Fresh $ f u v)
  0 ~~> (_      , Old _  ) = (0, None         )
  _ ~~> (Old u  , Old v  ) = (1, Old $ f u v  )
  _ ~~> (Fresh _, Old _  ) = (0, None         )
