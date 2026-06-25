{-|
Module      : Clash.Crypto.Cipher.AES.Specification.Properties
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Some properties that can be proven to be valid from the FIPS 197
specification.
-}

{-# LANGUAGE Safe #-}

module Clash.Crypto.Cipher.AES.Specification.Properties
  ( AESFacts(..)
  , KnownAES(..)
  ) where

import Clash.Prelude.Safe

import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Cipher.AES.Specification.Types
import Clash.Crypto.Cipher.AES.Specification.Algorithm

-- | We collect all required properties via the t'AESFacts' class.
data AESFacts (alg ∷ AES) where
  AESFacts ∷
    ( KnownNat (Nb alg)
    , KnownNat (Nk alg)
    , KnownNat (Nr alg)
    , KnownNat (AESBlockByteCount alg)
    , AESFunctions alg
    , 1 ≤ AESBlockByteCount alg
    , 1 ≤ AESBlockByteCount alg `Div` 8
    , 1 ≤ Nk alg -- due to the expansion algorithm
    , 1 ≤ Nr alg -- due to the expansion algorithm
    ) ⇒
    AESFacts alg

-- | We utilize the type checker to provide evidence for all of the
-- required properties, which are proven automatically for each
-- instance of the class.
class KnownAES alg
 where
  -- | Returns already proven evidence in form of a dictionary.
  knownAES ∷ ∀ x → x ~ alg ⇒ AESFacts alg

instance KnownAES AES128 where knownAES _ = AESFacts
instance KnownAES AES192 where knownAES _ = AESFacts
instance KnownAES AES256 where knownAES _ = AESFacts
