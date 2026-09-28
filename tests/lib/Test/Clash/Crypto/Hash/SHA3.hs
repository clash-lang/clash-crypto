{-|
Module      : Test.Clash.Crypto.Hash.SHA3
Copyright   : Copyright © 2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Shared test infrastructure for 'Clash.Crypto.Hash.SHA3'.
-}
{-# LANGUAGE MagicHash #-}

module Test.Clash.Crypto.Hash.SHA3
  ( -- * Utility Functions
    cryptoHash
    -- * Internal
  , CryptoHash(..)
  ) where

import Prelude

import GHC.TypeNats
import Data.Proxy (Proxy(..))
import Data.ByteString (ByteString, pack)
import Data.ByteArray (unpack)

import qualified Crypto.Hash

import Clash.Crypto.Hash.SHA3.Types

-- | Utility wrapper to instantiate the secure hashing implementations in
-- 'Crypto.Hash' using the 'SHA' selector of this package.
class CryptoHash (alg ∷ SHA3) where
  type CryptoToHash (alg ∷ SHA3)
  cryptoHash# ∷ Proxy alg → ByteString → Crypto.Hash.Digest (CryptoToHash alg)

instance CryptoHash SHA3_224 where
  type CryptoToHash SHA3_224 = Crypto.Hash.SHA3_224
  cryptoHash# _ = Crypto.Hash.hash

instance CryptoHash SHA3_256 where
  type CryptoToHash SHA3_256 = Crypto.Hash.SHA3_256
  cryptoHash# _ = Crypto.Hash.hash

instance CryptoHash SHA3_384 where
  type CryptoToHash SHA3_384 = Crypto.Hash.SHA3_384
  cryptoHash# _ = Crypto.Hash.hash

instance CryptoHash SHA3_512 where
  type CryptoToHash SHA3_512 = Crypto.Hash.SHA3_512
  cryptoHash# _ = Crypto.Hash.hash

instance KnownNat d => CryptoHash (SHAKE128 d) where
  type CryptoToHash (SHAKE128 d) = Crypto.Hash.SHAKE128 d
  cryptoHash# _ = Crypto.Hash.hash
instance KnownNat d => CryptoHash (SHAKE256 d) where
  type CryptoToHash (SHAKE256 d) = Crypto.Hash.SHAKE256 d
  cryptoHash# _ = Crypto.Hash.hash

-- | Hashes a bytestring according to the selected algorithm of type
-- 'SHA' using the primitives in 'Crypto.Hash'.
cryptoHash ∷
  ∀ (alg ∷ SHA3) → CryptoHash alg ⇒ ByteString → ByteString
cryptoHash alg = pack . unpack . cryptoHash# (Proxy @alg)
