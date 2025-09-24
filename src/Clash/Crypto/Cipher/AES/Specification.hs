{-|
Module      : Clash.Crypto.Cipher.AES.Specification
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Formalized AES specification according to
[FIPS PUB 197: Advanced Encryption Standard  (AES)](https://doi.org/10.6028/NIST.FIPS.197-upd1).

Note that this formalization adds an "@_@"-symbol to function names
that start with capital letter in the aforementioned document, to work
around the syntactic restrictions of Haskell. To keep the notation
consistent, the symbol is added to some function names starting with a
small letter as well.
-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}

module Clash.Crypto.Cipher.AES.Specification
  ( -- All functions that are present in the FIPS.
    AESFunctions(..),
    aesFunctional,
    -- Type of all specific AES functions.
    AES(..), 
    -- Verification
    KnownAES(..), AESFacts(..),
    -- Types
    InType, OutType, StateType, WType, 
    WordType, KeyType, Nr, Nk, Nb, WordSize,

    -- Definitions
    AESConstants, (⊕), RoundWType,
    subBytes, invSubBytes,
    mixColumns, invMixColumns,
    shiftRows, invShiftRows,
    addRoundKey, invAddRoundKey,
    -- Constants
    mX, aMixColumns, aInvMixColumns, xySBox, xyInvSBox
    --
    ,try
  ) where
import Clash.Prelude
import Data.Proxy (Proxy(..))

import Clash.Crypto.Cipher.AES.Specification.Properties
import Clash.Crypto.Cipher.AES.Specification.Algorithm
import Clash.Crypto.Cipher.AES.Specification.Constants
import Clash.Crypto.Cipher.AES.Specification.Definitions
import Clash.Crypto.Cipher.AES.Specification.Types

aesFunctional ∷ ∀ (alg ∷ AES) . KnownAES alg ⇒ Proxy alg →  InType alg → KeyType alg → OutType alg    
aesFunctional (alg ∷ Proxy alg) input key 
  | AESFacts{} ← knownAES @alg
  = cipher alg input (keyExpansion alg key)


key1AES192 ∷ KeyType AES192
key1AES192 = (0x8e:> 0x73:> 0xb0:> 0xf7:>Nil) :> (0xda:> 0x0e:> 0x64:> 0x52:> Nil) :> (0xc8:> 0x10:> 0xf3:> 0x2b:> Nil) :> (0x80:> 0x90:> 0x79:> 0xe5:>Nil) :> (0x62:> 0xf8:> 0xea:> 0xd2:> Nil) :> (0x52:> 0x2c:> 0x6b:> 0x7b:> Nil) :> Nil

try ∷ WType AES192
try = keyExpansion (Proxy @(AES192 ∷ AES)) key1AES192

try1 ∷ WType AES192
try1 = aesKeyExpansion  @(AES192 ∷ AES) key1AES192

aesKeyExpansion ∷ ∀ (alg ∷ AES) . KnownAES alg ⇒ KeyType alg → WType alg    
aesKeyExpansion  key 
  | AESFacts alg ← knownAES @alg
  = keyExpansion alg key
-- try ∷ WordType AES128
-- try = 0x09:> 0xcf:> 0x4f:> 0x3c:> Nil
-- -- subtry = xorWord (subWord (rotWord (Clash.Prelude.last key1AES128)))   (_Rcon (Proxy @(AES128 ∷ AES)) Clash.Prelude.!! 0)
-- subtry = subWord (rotWord (Clash.Prelude.last key1AES128))
-- t = (_Rcon (Proxy @(AES128 ∷ AES)) Clash.Prelude.!! 0)
-- xorT = xorWord subtry t