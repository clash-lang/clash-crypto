{-|
Module      : Test.Clash.Crypto.Hash.SHA
Copyright   : Copyright © 2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test specifics for 'Clash.Crypto.Hash.SHA'.
-}

{-# LANGUAGE MagicHash #-}

module Test.Clash.Crypto.Hash.SHA
  ( CryptoHash(..)
  , cryptoHash
  ) where

import Prelude

import Data.Proxy (Proxy(..))
import Data.ByteString (ByteString, pack)
import Data.ByteArray (unpack)

import Clash.Crypto.Hash.SHA
import qualified Crypto.Hash

class CryptoHash (alg ∷ SHA) where
  type CryptoToHash (alg ∷ SHA)
  cryptoHash# ∷ Proxy alg → ByteString → Crypto.Hash.Digest (CryptoToHash alg)

instance CryptoHash SHA1 where
  type CryptoToHash SHA1 = Crypto.Hash.SHA1
  cryptoHash# _ = Crypto.Hash.hash
instance CryptoHash SHA224 where
  type CryptoToHash SHA224 = Crypto.Hash.SHA224
  cryptoHash# _ = Crypto.Hash.hash
instance CryptoHash SHA256 where
  type CryptoToHash SHA256 = Crypto.Hash.SHA256
  cryptoHash# _ = Crypto.Hash.hash
instance CryptoHash SHA384 where
  type CryptoToHash SHA384 = Crypto.Hash.SHA384
  cryptoHash# _ = Crypto.Hash.hash
instance CryptoHash SHA512 where
  type CryptoToHash SHA512 = Crypto.Hash.SHA512
  cryptoHash# _ = Crypto.Hash.hash
instance CryptoHash SHA512224 where
  type CryptoToHash SHA512224 = Crypto.Hash.SHA512t_224
  cryptoHash# _ = Crypto.Hash.hash
instance CryptoHash SHA512256 where
  type CryptoToHash SHA512256 = Crypto.Hash.SHA512t_256
  cryptoHash# _ = Crypto.Hash.hash

cryptoHash ∷
 ∀ (alg ∷ SHA) → CryptoHash alg ⇒ ByteString → ByteString
cryptoHash alg = pack . unpack . cryptoHash# (Proxy @alg)
