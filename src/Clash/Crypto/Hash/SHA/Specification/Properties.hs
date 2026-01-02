{-|
Module      : Clash.Crypto.Hash.SHA.Specification.Properties
Copyright   : Copyright © 2024 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Some properties that can be proven to be valid from the FIPS 180-4
specification.
-}

module Clash.Crypto.Hash.SHA.Specification.Properties
  ( SHAFacts(..)
  , KnownSHA
  , knownSHA
  ) where

import Clash.Prelude.Safe

import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Hash.SHA.Specification.Types
import Clash.Crypto.Hash.SHA.Specification.Definitions

-- | We collect all required properties via the 'SHAFacts' class.
data SHAFacts (alg ∷ SHA) where
  SHAFacts ∷
    ( KnownNat (WordSize alg)
    , KnownNat (BlockSize alg)
    , KnownNat (HashValueWords alg)
    , KnownNat (MessageDigestSize alg)
    , KnownNat (ScheduleCount alg)
    , SHAInitials alg
    , SHAHashCompute alg
    , 1 ≤ BlockSize alg
    , 1 ≤ BlockSize alg `Div` 8
    , 1 ≤ ScheduleCount alg
    , 1 ≤ WordSize alg
    , 1 ≤ MessageDigestSize alg
    , 1 ≤ HashValueWords alg * WordSize alg
    , 2 ^ SizeBits alg
        ~ BlockSize alg * ((2 ^ SizeBits alg) `Div` BlockSize alg)
    , 2 * BlockSize alg ≤ (2 ^ SizeBits alg) `Div` BlockSize alg
    , MessageDigestSize alg ≤ HashValueWords alg * WordSize alg
    , MessageDigestSize alg ≤ BlockSize alg
    , BlockSize alg ~ 16 * WordSize alg
    , MessageDigestSize alg `Mod` 8 ~ 0
    ) ⇒
    SHAFacts alg

-- | We utilize the type checker to provide evidence for all of the
-- required properties, which are proven automatically for each
-- instance of the class.
class KnownSHA alg
 where
  knownSHA ∷ ∀ x → x ~ alg ⇒ SHAFacts alg

instance
 {-# DEPRECATED
   [ "SHA1 phases out by Dec. 31, 2030 and shall not be used in modern"
   , "applications any more (cf. https://doi.org/10.6028/NIST.SP.800-131Ar2)."
   ] #-} KnownSHA SHA1      where knownSHA _ = SHAFacts
instance KnownSHA SHA224    where knownSHA _ = SHAFacts
instance KnownSHA SHA256    where knownSHA _ = SHAFacts
instance KnownSHA SHA384    where knownSHA _ = SHAFacts
instance KnownSHA SHA512    where knownSHA _ = SHAFacts
instance KnownSHA SHA512224 where knownSHA _ = SHAFacts
instance KnownSHA SHA512256 where knownSHA _ = SHAFacts
