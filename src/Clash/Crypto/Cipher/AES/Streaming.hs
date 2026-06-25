{-|
Module      : Clash.Crypto.Blockcipher.AES.Streaming
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Streaming based implementation of
[FIPS PUB 197: Advanced Encryption Standard
(AES)](https://doi.org/10.6028/NIST.FIPS.197-upd1).
-}

module Clash.Crypto.Cipher.AES.Streaming
  ( aesECBencryption
  , aesECBdecryption
  , AESKeyExpansion(..)
  ) where

import Clash.Prelude.Safe

import Clash.Crypto.Cipher.AES.Streaming.Algorithm
import Clash.Crypto.Cipher.AES.Specification
import Clash.Signal.Channel

-- | AES encryption primitive.
aesECBencryption ∷
  HiddenClockResetEnable dom ⇒
  ∀ (alg ∷ AES) → (KnownAES alg, AESKeyExpansion alg) ⇒
  Channel dom (AESBlock alg, AESKey alg) →
  -- ^ input + key
  Channel dom (AESBlock alg)
  -- ^ response
aesECBencryption alg (unzipC → (inp, key))
  | AESFacts ← knownAES alg
  = cipherStream alg
  $ zipC inp
  $ keyExpansionStream alg key

-- | AES decryption primitive.
aesECBdecryption ∷
  HiddenClockResetEnable dom ⇒
  ∀ (alg ∷ AES) → (KnownAES alg, AESKeyExpansion alg) ⇒
  Channel dom (AESBlock alg, AESKey alg) →
  -- ^ input + key
  Channel dom (AESBlock alg)
  -- ^ response
aesECBdecryption alg (unzipC → (inp, key))
  | AESFacts ← knownAES alg
  = invCipherStream alg
  $ zipC inp
  $ keyExpansionStream alg key
