{-|
Module      : Clash.Crypto.Cipher.AES.Streaming.Combinatorial
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

AES purely combinatorial according to
[FIPS PUB 197: Advanced Encryption Standard  (AES)](https://doi.org/10.6028/NIST.FIPS.197-upd1).
-}

{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.Cipher.AES.Streaming.Combinatorial
  ( combinatorialAES
  ) where


import Data.Proxy (Proxy)


import Clash.Crypto.Cipher.AES.Specification
-- Interface liberies:
import Clash.Prelude
import Clash.Signal.Channel
import Clash.Signal.DataStream
import Clash.Signal.Extra (apWhen, regEnN)

import Data.Constraint.Nat.Extra (CancelMultiple, KeepsPositiveIfMultiple)

import Data.Proxy (Proxy)




combinatorialAES ∷ ∀ (alg ∷ AES) dom.
    ( KnownAES alg, HiddenClockResetEnable dom) ⇒
    Channel dom (InType alg, KeyType alg) →
    -- ^ input stream ^ key stream
    Channel dom (OutType alg)
    -- ^ response channel
combinatorialAES input
  | AESFacts alg <- knownAES @alg
  = fmap
      (\(pt, key) -> cipher alg pt (keyExpansion alg key))
      input

