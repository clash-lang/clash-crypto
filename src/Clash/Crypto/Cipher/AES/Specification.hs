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
    InType, OutType, StateType,
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


key1AES128 ∷ KeyType AES128
key1AES128 = (0x2b:> 0x7e:> 0x15:> 0x16:>Nil) :> (0x28:> 0xae:> 0xd2:> 0xa6:> Nil) :> (0xab:> 0xf7:> 0x15:> 0x88:> Nil) :> (0x09:> 0xcf:> 0x4f:> 0x3c:> Nil) :> Nil

try ∷ WType AES128
try = keyExpansion (Proxy @(AES128 ∷ AES)) key1AES128

try1 ∷ WType AES128
try1 = aesKeyExpansion  @(AES128 ∷ AES) key1AES128

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