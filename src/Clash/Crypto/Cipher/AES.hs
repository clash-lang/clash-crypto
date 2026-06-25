{-|
Module      : Clash.Crypto.Cipher.AES
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Streaming based blockcipher algorithms according to
[FIPS PUB 197: Advanced Encryption Standard
(AES)](https://doi.org/10.6028/NIST.FIPS.197-upd1).
-}

module Clash.Crypto.Cipher.AES
  ( -- * Streaming Implementation
    AES(..)
  , AESKeyExpansion(..)
  , aesECBencryption
  , aesECBdecryption
    -- * Types
  , Byte, AESWord, AESWordByteCount, Nk, Nb, Nr
  , AESBlock, AESBlockByteCount, AESRoundKey, AESKey, AESState
    -- * Definitions
  , (⊕), subBytes, invSubBytes, mixColumns, invMixColumns,
    shiftRows, invShiftRows, addRoundKey, invAddRoundKey
    -- * Additional Evidence
  , KnownAES(..), AESFacts(..)
  ) where

import Clash.Crypto.Cipher.AES.Specification
import Clash.Crypto.Cipher.AES.Streaming
