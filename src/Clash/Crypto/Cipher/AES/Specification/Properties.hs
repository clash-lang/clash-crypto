{-|
Module      : Clash.Crypto.Cipher.AES.Specification.Properties
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Some properties that can be proven to be valid from the FIPS 197
specification.
-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
module Clash.Crypto.Cipher.AES.Specification.Properties
  ( AESFacts(..)
  , KnownAES(..)
  ) where

import Clash.Prelude

import Data.Proxy (Proxy(..))
import Language.Haskell.Unicode (type (≤))
import Clash.Crypto.Cipher.AES.Specification.Types
import Clash.Crypto.Cipher.AES.Specification.Algorithm
-- | We collect all required properties via the 'AESFacts' class.
-- | In chapter 6 the constraints are defined.
data AESFacts (alg ∷ AES) where
  AESFacts ∷
    ( KnownNat (WordSize alg)
    , KnownNat (Nb alg)
    , KnownNat (BlockSize alg)
    , KnownNat (Nk alg)
    , KnownNat (KeyLength alg)
    , KnownNat (Nr alg)
    -- , AESInitials alg
    , AESFunctions alg
    , 1 ≤ BlockSize alg
    , 1 ≤ BlockSize alg `Div` 8
    -- , 1 ≤ ScheduleCount alg
    , 1 ≤ WordSize alg
    , 1 ≤ Nk alg -- due to the expansion algorithm
    , 1 ≤ Nr alg -- due to the expansion algorithm
    -- , 1 ≤ MessageDigestSize alg
    -- , 1 ≤ HashValueWords alg * WordSize alg
    -- , 2 ^ SizeBits alg
    --     ~ BlockSize alg * ((2 ^ SizeBits alg) `Div` BlockSize alg)
    -- , 2 * BlockSize alg ≤ (2 ^ SizeBits alg) `Div` BlockSize alg
    -- , MessageDigestSize alg ≤ HashValueWords alg * WordSize alg
    -- , MessageDigestSize alg ≤ BlockSize alg
    -- , BlockSize alg ~ 16 * WordSize alg
    -- , MessageDigestSize alg `Mod` 8 ~ 0
    ) ⇒
    Proxy alg →
    AESFacts alg

-- | We utilize the type checker to provide evidence for all of the
-- required properties, which are proven automatically for each
-- instance of the class.
class    KnownAES alg       where knownAES ∷ AESFacts alg
instance KnownAES AES128    where knownAES = AESFacts Proxy
instance KnownAES AES192    where knownAES = AESFacts Proxy
instance KnownAES AES256    where knownAES = AESFacts Proxy
