{-|
Module      : Clash.Crypto.Cipher.AES
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Streaming based blockcipher algorithms according to
[FIPS PUB 197: Advanced Encryption Standard  (AES)](https://doi.org/10.6028/NIST.FIPS.197-upd1).
-}
{-# LANGUAGE UnicodeSyntax #-}

module Clash.Crypto.Cipher.AES
  ( -- All functions that are present in the FIPS.
    AESFunctions(..),
    -- Type of all specific AES functions.
    AES,
    -- Verification
    KnownAES(..),
    AESFacts(..),
    -- Types
    InType, OutType, StateType,
    WordType,
  ) where

import Clash.Prelude
import Clash.Signal.Channel
import Clash.Signal.DataStream

import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Cipher.AES.Specification
import Clash.Crypto.Cipher.AES.Streaming


-- | Reads serialized messages from an input stream, calculates their
-- secure hash and releases the result on the returned channel
-- afterwards.

-- Input messages may be separated into multiple n-bit frames, where
-- the end frame of each message also holds the amount of *unused*
-- bits that have been added as LSBs to align with the frame size
-- @n@. Note that the first bit of the end frame is always part of the
-- message.

-- The digset relased on the channel is calculated according to the
-- selected hash algorithm. It is released after the arrival of a
-- message's end frame and the calculation of the hash.
aes ∷
  ∀ (alg ∷ AES) (dom ∷ Domain) (n ∷ Nat).
  (KnownAES alg, KnownDomain dom, HiddenClockResetEnable dom) ⇒
  (KnownNat n, 1 ≤ n, n ≤ BlockSize alg, Mod (BlockSize alg) n ~ 0) ⇒
  DataStream dom () (Index n) (BitVector n) →
  -- ^ streamed input messages
  Channel dom (Digest alg)
  -- ^ result channel
aes
  | AESFacts{} ← knownAES @alg
  = aesStream @alg @dom @n
