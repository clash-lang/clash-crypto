{-|
Module      : Clash.Crypto.Hash.SHA
Copyright   : Copyright © 2024-2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Streaming based secure hash algorithms according to
[FIPS PUB 180-4: Secure Hash Standard (SHS)](http://dx.doi.org/10.6028/NIST.FIPS.180-4).
-}

module Clash.Crypto.Hash.SHA
  ( -- * Streaming Implementation
    SHA(..)
  , Digest
  , sha
  , -- * Sizes & Utility Types
    WordSize, BlockSize, MessageDigestSize, HashValueWords
  , ScheduleCount, SHAWord, MessageBlock, HashValue, Message
    -- * Additional Evidence
  , KnownSHA(..), SHAFacts(..)
  ) where

import Clash.Prelude.Safe
import Clash.Signal.Channel
import Clash.Signal.DataStream

import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Hash.SHA.Specification
import Clash.Crypto.Hash.SHA.Streaming
import Clash.Crypto.Hash.SHA.Streaming.Padding

-- | Reads serialized messages from an input stream, calculates their
-- secure hash and releases the result on the returned channel
-- afterwards.
--
-- Input messages may be separated into multiple n-bit frames, where
-- the end frame of each message also holds the amount of *unused*
-- bits that have been added as LSBs to align with the frame size
-- @n@. Note that the first bit of the end frame is always part of the
-- message.
--
-- The digest relased on the channel is calculated according to the
-- selected hash algorithm. It is released after the arrival of a
-- message's end frame and the calculation of the hash.
sha ∷
  ∀ (n ∷ Nat) (dom ∷ Domain).
  (KnownNat n, HiddenClockResetEnable dom, 1 ≤ n) ⇒
  ∀ (alg ∷ SHA) → KnownSHA alg ⇒
  (n ≤ BlockSize alg, Mod (BlockSize alg) n ~ 0) ⇒
  DataStream dom () (Index n) (BitVector n) →
  -- ^ streamed input messages
  Channel dom (Digest alg)
  -- ^ result channel
sha alg
  = fmap (toDigest alg)
  . hashStream alg
  . padMessageStream alg
