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
  (   AESStreamFacts(..)
    , KnownAESStream(..)
    , aesECBencryption
    , aesECBdecryption
    , AESKeyExpansion(..)
  ) where
import Clash.Crypto.Cipher.AES.Streaming.Properties
import Clash.Crypto.Cipher.AES.Streaming.Algorithm as Alg
import Clash.Crypto.Cipher.AES.Specification as Spec
import Clash.Prelude
import Clash.Signal.Channel

aesECBencryption ∷ ∀ (alg ∷ Spec.AES) dom. (Spec.KnownAES alg,  KnownAESStream alg, AESKeyExpansion alg, HiddenClockResetEnable dom) ⇒     
    Channel dom (Spec.InType alg, Spec.KeyType alg) →
    -- ^ input stream ^ key stream
    Channel dom (Spec.OutType alg)
    -- ^ response channel  
aesECBencryption input
  | AESStreamFacts{} ← knownAESStream @alg
  =  Alg.cipher @alg (zipC (fst unzipInput) expansion)
    where
      expansion = Alg.keyExpansion @alg (snd unzipInput)
      unzipInput = unzipC input

aesECBdecryption ∷ ∀ (alg ∷ Spec.AES) dom. (Spec.KnownAES alg,  KnownAESStream alg, AESKeyExpansion alg, HiddenClockResetEnable dom) ⇒     
    Channel dom (Spec.InType alg, Spec.KeyType alg) →
    -- ^ input stream ^ key stream
    Channel dom (Spec.OutType alg)
    -- ^ response channel  
aesECBdecryption input
  | AESStreamFacts{} ← knownAESStream @alg
  =  Alg.invCipher @alg (zipC (fst unzipInput) expansion)
    where
      expansion = Alg.keyExpansion @alg (snd unzipInput)
      unzipInput = unzipC input

