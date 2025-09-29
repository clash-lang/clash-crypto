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
    AESFunctions(..),AESFacts(..), KnownAES(..),
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
  ) where
import Clash.Prelude
import Data.Proxy (Proxy(..))

import Clash.Crypto.Cipher.AES.Specification.Properties
import Clash.Crypto.Cipher.AES.Specification.Algorithm
import Clash.Crypto.Cipher.AES.Specification.Constants
import Clash.Crypto.Cipher.AES.Specification.Definitions
import Clash.Crypto.Cipher.AES.Specification.Types

aesFunctional ∷ ∀ (alg ∷ AES) . KnownAES alg ⇒ InType alg → KeyType alg → OutType alg    
aesFunctional input key 
  | AESFacts alg ← knownAES @alg
  = cipher alg input (keyExpansion alg key)

key1AES128 ∷ KeyType AES128
key1AES128 = (0x2b:> 0x7e:> 0x15:> 0x16:>Nil) :> (0x28:> 0xae:> 0xd2:> 0xa6:> Nil) :> (0xab:> 0xf7:> 0x15:> 0x88:> Nil) :> (0x09:> 0xcf:> 0x4f:> 0x3c:> Nil) :> Nil
in1AES128 ∷ InType AES128
in1AES128 = (0x32:> 0x43:> 0xf6:> 0xa8:>Nil) :> (0x88:> 0x5a:> 0x30:> 0x8d:> Nil) :> (0x31:> 0x31 :> 0x98:> 0xa2:> Nil) :> (0xe0 :> 0x37:> 0x07:> 0x34:> Nil) :> Nil
w1AES128 ∷ WType AES128
w1AES128 = keyExpansion (Proxy @(AES128 :: AES)) key1AES128

try1 ∷ OutType AES128
try1 = aesFunctional  @(AES128 ∷ AES) in1AES128 key1AES128 
try ∷  InType AES128 → KeyType AES128 → OutType AES128
try input key = cipher  (Proxy @(AES128:: AES)) input (keyExpansion  (Proxy @(AES128:: AES)) key)

key1AES256 ∷  KeyType AES256
key1AES256 = (0x60:> 0x3d:> 0xeb:> 0x10:>Nil) :> (0x15:> 0xca:> 0x71:> 0xbe:> Nil) :> (0x2b:> 0x73:> 0xae:> 0xf0:> Nil) :> (0x85:> 0x7d:> 0x77:> 0x81:>Nil) :> (0x1f:> 0x35:> 0x2c:> 0x07:>Nil) :> (0x3b:> 0x61:> 0x08:> 0xd7:> Nil) :> (0x2d:> 0x98:> 0x10:> 0xa3:> Nil) :> (0x09:> 0x14:> 0xdf:> 0xf4:>Nil)  :> Nil



try2 ∷ Proxy AES128 → InType AES128 → WType AES128 → StateType AES128
try2 _ input w1s= addRoundKey (shiftRows (subBytes (rounds input w1s))) (last (wInWords w1s))
  where 
    rounds ∷ InType AES128 → WType AES128 → StateType AES128
    rounds input1 ws = foldl mutation (addRoundKey  input1 (head (wInWords ws))) (init (tail (wInWords ws)))
    wInWords ∷ WType AES128 → Vec (Nr AES128 + 1) (RoundWType AES128)
    wInWords = unconcat (SNat ∷ SNat (Nb AES128 ))
    mutation ∷ StateType alg → RoundWType alg → StateType alg
    mutation state = addRoundKey (mixColumns ( shiftRows (subBytes state))) 
-- try1 ∷ WType AES256
-- try1 = aesKeyExpansion  @(AES256 ∷ AES) key1AES256

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