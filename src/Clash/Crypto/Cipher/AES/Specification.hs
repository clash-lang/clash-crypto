{-|
Module      : Clash.Crypto.Cipher.AES.Specification
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Formalized AES specification according to
[FIPS PUB 197: Advanced Encryption Standard
(AES)](https://doi.org/10.6028/NIST.FIPS.197-upd1).
-}

module Clash.Crypto.Cipher.AES.Specification
  ( -- * Functions from the FIPS standard
    AESFunctions(..)
  , aesFunctional
    -- * Additional Evidence
  , KnownAES(..), AESFacts(..)
    -- * Types
  , AES(..), Byte, AESWord, AESWordByteCount, Nr, Nk, Nb
  , AESBlock, AESBlockByteCount, AESKey, AESRoundKey
  , AESState, KeySchedule
    -- * Definitions
  , (⊕), subBytes, invSubBytes
  , mixColumns, invMixColumns
  , shiftRows, invShiftRows
  , addRoundKey, invAddRoundKey
    -- * Constants
  , aMixColumns, aInvMixColumns, xySBox, xyInvSBox
  ) where

import Clash.Crypto.Cipher.AES.Specification.Properties
import Clash.Crypto.Cipher.AES.Specification.Algorithm
import Clash.Crypto.Cipher.AES.Specification.Constants
import Clash.Crypto.Cipher.AES.Specification.Definitions
import Clash.Crypto.Cipher.AES.Specification.Types

-- | Purely functional reference implementation.
aesFunctional ∷
  ∀ (alg ∷ AES) → KnownAES alg ⇒
  AESBlock alg → AESKey alg → AESBlock alg
aesFunctional alg input key
  | AESFacts ← knownAES alg
  = cipher alg input (keyExpansion alg key)
