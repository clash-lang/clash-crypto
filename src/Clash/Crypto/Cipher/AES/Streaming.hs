{-|
Module      : Clash.Crypto.Blockcipher.AES.Streaming
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Streaming based implementation of FIPS 197,
[FIPS PUB 197: Advanced Encryption Standard  (AES)](https://doi.org/10.6028/NIST.FIPS.197-upd1).
-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.Cipher.AES.Streaming
  ( aesStream
  ) where

import Clash.Prelude
import Clash.Signal.Channel
import Clash.Signal.DataStream
import Clash.Signal.Delayed.Extra
import Clash.Signal.Extra (apWhen)

import Data.Constraint.Nat.Extra (DDiv, CancelMultiple, KeepsPositiveIfMultiple)
import GHC.TypeNats.Proof (Rewrite(..), using)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Cipher.AES.Specification
-- import Clash.Crypto.Hash.SHA.Streaming.Stages

aesStream ∷ 
    ∀ (alg ∷ AES) dom.
    (KnownAES alg, HiddenClockResetEnable dom
    , 4 ≤  Blocksize alg, Mod (BlockSize alg) 4 ~ 0)
    ⇒
    DataStream dom (Index ((BlockSize alg `Div` 4) + 1)) () (WordType) →
    -- ^ input stream
    Channel dom (Digest alg)
    -- ^ response channel
aesStream
