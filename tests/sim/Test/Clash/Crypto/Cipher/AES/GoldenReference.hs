{-|
Module      : Test.Clash.Crypto.Cipher.AES.Specification
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Test suite for 'Clash.Crypto.Cipher.AES'.
-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedLists #-} -- Used to inturper a list as Byte String
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}

module Test.Clash.Crypto.Cipher.AES.GoldenReference (CryptoAES(..)) where

import Clash.Crypto.Cipher.AES
import Clash.Prelude
import Clash.Signal.Channel
import Clash.Signal.DataStream
import Clash.Sized.Vector (unsafeFromList)

-- https://hackage.haskell.org/package/clash-prelude-hedgehog
import Hedgehog
import qualified Hedgehog.Gen as Gen

import Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog

import Data.Proxy (Proxy(..))
import Clash.Hedgehog.Sized.BitVector (genDefinedBitVector)
import Clash.Hedgehog.Sized.Vector
import Clash.Hedgehog.Sized.Unsigned (genUnsigned)
import qualified Test.Clash.Crypto.Cipher.AES.Specification.Definitions as Def
import qualified Test.Clash.Crypto.Cipher.AES.Specification.Algorithm as Alg
-- Test AES128
import Crypto.Cipher.AES as Reference (AES128, AES192, AES256) 
import Crypto.Cipher.Types
import Crypto.Error

import qualified Crypto.Random.Types as CRT

import Data.ByteString (ByteString) 
import Crypto.Cipher.AES 
import Crypto.Cipher.Types 
import Crypto.Random (getRandomBytes)
import Crypto.Error (throwCryptoError)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as C8

import qualified Clash.Crypto.Cipher.AES.Specification as Spec
class CryptoAES (alg ∷ Spec.AES) where
  encryptoECB :: Proxy alg -> ByteString -> ByteString -> ByteString
  decryptoECB :: Proxy alg -> ByteString -> ByteString -> ByteString
instance CryptoAES Spec.AES128      where 
  encryptoECB ∷ Proxy alg → ByteString -> ByteString -> ByteString
  encryptoECB _ key plainText = case cipherInit key of
    CryptoPassed (cipher1 :: AES128) -> ecbEncrypt cipher1 plainText
    CryptoFailed cipher1 -> error ("Cipher initialization failed" <> show cipher1)
  decryptoECB ∷ Proxy alg → ByteString -> ByteString -> ByteString
  decryptoECB _ key cipherText = case cipherInit key of
    CryptoPassed (cipher1 ∷ AES128)-> ecbDecrypt cipher1 cipherText
    CryptoFailed cipher1 -> error ("Cipher initialization failed" <> show cipher1)


instance CryptoAES Spec.AES192    where
  encryptoECB ∷ Proxy alg → ByteString -> ByteString -> ByteString
  encryptoECB _ key plainText = case cipherInit key of
    CryptoPassed (cipher1 :: AES192) -> ecbEncrypt cipher1 plainText
    CryptoFailed cipher1 -> error ("Cipher initialization failed" <> show (cipher1, BS.length key))
  decryptoECB ∷ Proxy alg → ByteString -> ByteString -> ByteString
  decryptoECB _ key cipherText = case cipherInit key of
    CryptoFailed _ -> error "Cipher initialization failed"
    CryptoPassed (cipher1 ∷ AES192)-> ecbDecrypt cipher1 cipherText

instance CryptoAES Spec.AES256    where 
  encryptoECB ∷ Proxy alg → ByteString -> ByteString -> ByteString
  encryptoECB _ key plainText = case cipherInit key of
    CryptoPassed (cipher1 :: AES256) -> ecbEncrypt cipher1 plainText
    CryptoFailed cipher1 -> error ("Cipher initialization failed" <> show (cipher1, BS.length key))

  decryptoECB ∷ Proxy alg → ByteString -> ByteString -> ByteString
  decryptoECB _ key cipherText = case cipherInit key of
    CryptoFailed _ -> error "Cipher initialization failed"
    CryptoPassed (cipher1 ∷ AES256)-> ecbDecrypt cipher1 cipherText