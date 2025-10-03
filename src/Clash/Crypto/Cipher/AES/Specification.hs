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

