{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.Hash.SHA
  ( SHA(..), WordSize, BlockSize, MessageDigestSize, HashValueWords
  , ScheduleCount, SHAWord, MessageBlock, HashValue, Message
  , KnownSHA(..), SHAFacts(..)
  , sha
  ) where

import Clash.Prelude

import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Hash.SHA.Specification
import Clash.Crypto.Hash.SHA.Streaming
import Clash.Crypto.Hash.SHA.Streaming.Padding

sha ∷
  ∀ (alg ∷ SHA) (dom ∷ Domain) (n ∷ Nat).
  (KnownSHA alg, KnownDomain dom, HiddenClockResetEnable dom) ⇒
  (KnownNat n, 1 ≤ n, n ≤ BlockSize alg, Mod (BlockSize alg) n ~ 0) ⇒
  Signal dom (Maybe (BitVector n, Maybe (Index (n + 1)))) →
  -- ^ Input stream for passing messages, where each message may be
  -- separated into multiple n-bit frames. The messages are only
  -- composed out of the 'Just' wrapped data values passed to the
  -- stream, i.e., any intermediate 'Nothing' values will be
  -- ignored. The first component of each 'Just' value contains the
  -- actual data frame, while the second component is used to indicate
  -- the end of a message. Once the end of a message is reached, the
  -- second component also holds the amount of *unused* bits that have
  -- been added as LSBs to align with the frame size @n@.
  --
  -- Note that all of the last frame's data bits can be marked as
  -- unused. In that case, the message already was terminated by the
  -- previous frame and the current frame only serves as an
  -- end-of-message indicator. The same way, all bits of the frame can
  -- be used via marking none of the bits as unused. This way, the
  -- user is free in the choice of message termination system he likes
  -- to apply.
  Signal dom (Maybe (BitVector (MessageDigestSize alg)))
  -- ^ The response stream providing a @Just messageDigest@ as soon as
  -- the hash has been computed (after arrival of a terminated
  -- message).
sha
  = fmap (fmap (toDigest @alg))
  . toSignal
  . hashStream @alg
  . fromSignal
  . padMessageStream @alg
