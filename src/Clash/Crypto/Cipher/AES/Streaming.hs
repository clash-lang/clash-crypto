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
  ( AESFacts(..)
  , KnownAES(..)
  ) where


import Data.Proxy (Proxy)

-- import GHC.TypeNats.Proof (Rewrite(..), using)
import Clash.Crypto.Cipher.AES.Streaming.Properties
import Clash.Crypto.Cipher.AES.Specification
-- Interface liberies:
import Clash.Prelude
import Clash.Signal.Channel
import Clash.Signal.DataStream
import Clash.Signal.Extra (apWhen, regEnN)

import Data.Constraint.Nat.Extra (CancelMultiple, KeepsPositiveIfMultiple)
aesCipher ∷ ∀ (alg ∷ AES) . KnownAES alg ⇒ Proxy alg →  InType alg → KeyType alg → OutType alg    
aesCipher (alg ∷ Proxy alg) input key 
  | AESFacts{} ← knownAES @alg
  = cipher alg input (keyExpansion alg key)

-- aesStream ∷ 
--     ∀ (alg ∷ AES) dom.
--     (KnownAES alg, HiddenClockResetEnable dom
--     , 4 ≤  Blocksize alg, Mod (BlockSize alg) 4 ~ 0)
--     ⇒
--     DataStream dom (Index ((BlockSize alg `Div` 4) + 1)) () (InType alg) →
--     -- ^ input stream
--     Channel dom (OutType alg)
--     -- ^ response channel
-- aesStream
