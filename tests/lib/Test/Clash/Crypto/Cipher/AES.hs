{-|
Module      : Test.Clash.Crypto.Cipher.AES
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Shared test infrastructure for 'Clash.Crypto.Cipher.AES'.
-}

module Test.Clash.Crypto.Cipher.AES
  ( CryptoAES(..)
  ) where

import Clash.Prelude.Safe

import Data.ByteString (ByteString)
import Crypto.Cipher.Types (cipherInit, ecbEncrypt, ecbDecrypt)
import Crypto.Error (CryptoFailable(..))

import qualified Crypto.Cipher.AES as Reference (AES128, AES192, AES256)

import Clash.Crypto.Cipher.AES.Specification (AES(..))

-- | Class based interface to the golden reference for AES encryption
-- and decryption from the @crypton@ library.
class CryptoAES (alg ∷ AES) where
  encryptoECB ∷ ∀ x → x ~ alg ⇒ ByteString → ByteString → ByteString
  decryptoECB ∷ ∀ x → x ~ alg ⇒ ByteString → ByteString → ByteString

instance CryptoAES AES128 where
  encryptoECB _ key plainText
    = withCrypto ecbEncrypt plainText
    $ cipherInit @Reference.AES128 key

  decryptoECB _ key cipherText
    = withCrypto ecbDecrypt cipherText
    $ cipherInit @Reference.AES128 key

instance CryptoAES AES192 where
  encryptoECB _ key plainText
    = withCrypto ecbEncrypt plainText
    $ cipherInit @Reference.AES192 key

  decryptoECB _ key cipherText
    = withCrypto ecbDecrypt cipherText
    $ cipherInit @Reference.AES192 key

instance CryptoAES AES256 where
  encryptoECB _ key plainText
    = withCrypto ecbEncrypt plainText
    $ cipherInit @Reference.AES256 key

  decryptoECB _ key cipherText
    = withCrypto ecbDecrypt cipherText
    $ cipherInit @Reference.AES256 key

withCrypto ∷ (a → b → c) → b → CryptoFailable a → c
withCrypto action input = \case
  CryptoPassed cipher → action cipher input
  CryptoFailed cipher → error $ "Cipher initialization failed: "
                             <> show cipher
