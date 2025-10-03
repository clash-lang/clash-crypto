{-|
Module      : Clash.Crypto.Cipher.AES
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Streaming based blockcipher algorithms according to
[FIPS PUB 197: Advanced Encryption Standard  (AES)](https://doi.org/10.6028/NIST.FIPS.197-upd1).
-}
{-# LANGUAGE UnicodeSyntax #-}

module Clash.Crypto.Cipher.AES
  ( -- All functions that are present in the FIPS.
    -- Type of all specific AES functions.
    AES(..),
    -- Verification
    KnownAES(..),
    AESFacts(..),
    -- Types
    InType, OutType, KeyType, StateType,
    WordType, RoundWType, WordSize, Nk, Nb, Nr,
    -- Definitions
    (⊕), subBytes, invSubBytes,
    mixColumns, invMixColumns,
    shiftRows, invShiftRows,
    addRoundKey, invAddRoundKey
    -- Streaming
    , aesECBencryption
    , aesECBdecryption
    , AESKeyExpansion(..)
  ) where



import Clash.Crypto.Cipher.AES.Specification
import Clash.Crypto.Cipher.AES.Streaming
