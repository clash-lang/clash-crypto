{-|
Module      : Clash.Crypto.Hash.SHA3.Types
Copyright   : Copyright © 2026 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Definition of sha3 algorithms and related types.
-}
module Clash.Crypto.Hash.SHA3.Types where

import Clash.Prelude.Safe hiding (type (^))

-- | Supported hash algorithms.
data SHA3 where
  SHA3_224 ∷ SHA3
  SHA3_256 ∷ SHA3
  SHA3_384 ∷ SHA3
  SHA3_512 ∷ SHA3
  SHAKE128 ∷ Nat → SHA3
  SHAKE256 ∷ Nat → SHA3
    deriving
    ( Generic
    , NFDataX
    , Eq
    , Show
    )

-- | Output digest size per algorithm.
type MessageDigestSize ∷ SHA3 → Nat
type family MessageDigestSize alg where
  MessageDigestSize SHA3_224     = 224
  MessageDigestSize SHA3_256     = 256
  MessageDigestSize SHA3_384     = 384
  MessageDigestSize SHA3_512     = 512
  MessageDigestSize (SHAKE128 d) = d
  MessageDigestSize (SHAKE256 d) = d

-- | The digest resulting from the applied hashing function.
type Digest alg = BitVector (MessageDigestSize alg)

-- | Definition of the input Message type.
type Message (l :: Nat) = BitVector l

-- | Define the ℓ parameter of the state based on the algorithm.
type AlgStateL alg = 6
-- | Define the width of the state based on the algorithm.
type AlgStateW alg = 64
-- | Define the sizes of the state based on the algorithm.
type AlgStateSize alg = 1600

-- | Capacity size to be provided to the KECCAK[c] per hashing algorithm.
type AlgCapacity ∷ SHA3 → Nat
type family AlgCapacity alg where
  AlgCapacity SHA3_224     = 448
  AlgCapacity SHA3_256     = 512
  AlgCapacity SHA3_384     = 768
  AlgCapacity SHA3_512     = 1024
  AlgCapacity (SHAKE128 _) = 256
  AlgCapacity (SHAKE256 _) = 512

-- | Rate for the given state size and capacity.
type Rate b c = b - c

-- | Rate for the given algorithm.
type AlgRate alg = Rate (AlgStateSize alg) (AlgCapacity alg)

-- | Given a message of length @m@ and a rate @x@,
-- @ReqZerosPadding x m@ provides the number of
-- zeros that need to be added in the padding.
type ReqZerosPadding ∷ Nat → Nat → Nat
type ReqZerosPadding x m = (x - ((m + 2) `Mod` x)) `Mod` x

-- | Given a message length @m@ and a rate @x@,
-- @Pad101Size x m@ provides the size of 10*1 the padding.
type Pad101Size ∷ Nat → Nat → Nat
type Pad101Size x m = ReqZerosPadding x m + 2
