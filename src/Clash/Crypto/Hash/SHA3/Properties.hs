{-|
Module      : Clash.Crypto.Hash.SHA3.Properties
Copyright   : Copyright © 2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Definitions capturing basic properties of the SHA3 algorithms.
-}
{-# LANGUAGE UndecidableInstances #-}
module Clash.Crypto.Hash.SHA3.Properties
  ( SHA3Facts(..)
  , KnownSHA3 (..)
  , SuffixConstants(..)
  ) where

import Clash.Sized.BitVector (BitVector)

import Data.Type.Equality (type (~))
import GHC.TypeLits
import GHC.TypeNats.Proof
import GHC.TypeLits.KnownNat (KnownBool)
import Language.Haskell.Unicode (type (≤))

import Clash.Crypto.Hash.SHA3.Types
import Clash.Crypto.Hash.SHA3.State (KnownStateL)

-- | A data type that holds all the constraints
-- for a given algorithm's related values.
data SHA3Facts (alg ∷ SHA3) where
  SHA3Facts ∷
    ( KnownNat (MessageDigestSize alg)
    , 1 ≤ MessageDigestSize alg
    , MessageDigestSize alg `Mod` 8 ~ 0
    , KnownNat (AlgCapacity alg)
    , 1 ≤ AlgCapacity alg
    , AlgCapacity alg < 1600
    , KnownNat (AlgRate alg)
    , AlgRate alg `Mod` 8 ~ 0
    , KnownBool (MessageDigestSize alg `Mod` AlgRate alg == 0)
    , 25 ≤ Div (AlgRate alg) 8
    , SuffixConstants alg
    , KnownNat (SuffixLen alg)
    , KnownStateL (AlgStateL alg)
    ) ⇒ SHA3Facts alg

-- | We utilize the type checker to provide evidence for all of the
-- required properties, which are proven automatically for each
-- instance of the class.
class KnownSHA3 alg
 where
  -- | Returns already proven evidence in form of a dictionary.
  knownSHA3 ∷ ∀ x → x ~ alg ⇒ SHA3Facts alg

instance KnownSHA3 SHA3_224     where knownSHA3 _ = SHA3Facts
instance KnownSHA3 SHA3_256     where knownSHA3 _ = SHA3Facts
instance KnownSHA3 SHA3_384     where knownSHA3 _ = SHA3Facts
instance KnownSHA3 SHA3_512     where knownSHA3 _ = SHA3Facts
instance
  ( KnownNat d
  , 1 ≤ d
  , d `Mod` 8 ~ 0
  , KnownBool (d `Mod` AlgRate (SHAKE128 d) == 0)
  ) ⇒ KnownSHA3 (SHAKE128 d) where
  knownSHA3 _ = SHA3Facts
instance
  ( KnownNat d
  , 1 ≤ d
  , d `Mod` 8 ~ 0
  , KnownBool (d `Mod` AlgRate (SHAKE256 d) == 0)
  ) ⇒ KnownSHA3 (SHAKE256 d) where
  knownSHA3 _ = SHA3Facts

-- | A type class that provides information about
-- the message suffix to be applied before padding.
class SuffixConstants (alg ∷ SHA3) where
  -- | The length of the suffix in bits.
  type SuffixLen alg ∷ Nat
  -- | The suffix to be applied.
  suffix ∷ ∀ x → x ~ alg ⇒ BitVector (SuffixLen alg)

instance SuffixConstants SHA3_224 where
  type SuffixLen SHA3_224 = 2
  suffix _ = 0b_01 ∷ BitVector 2
instance SuffixConstants SHA3_256 where
  type SuffixLen SHA3_256 = 2
  suffix _ = 0b_01 ∷ BitVector 2
instance SuffixConstants SHA3_384 where
  type SuffixLen SHA3_384 = 2
  suffix _ = 0b_01 ∷ BitVector 2
instance SuffixConstants SHA3_512 where
  type SuffixLen SHA3_512 = 2
  suffix _ = 0b_01 ∷ BitVector 2
instance SuffixConstants (SHAKE128 d) where
  type SuffixLen (SHAKE128 _) = 4
  suffix _ = 0b1111 ∷ BitVector 4
instance SuffixConstants (SHAKE256 d) where
  type SuffixLen (SHAKE256 _) = 4
  suffix _ = 0b1111 ∷ BitVector 4
