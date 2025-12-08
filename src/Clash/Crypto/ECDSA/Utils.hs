{-# LANGUAGE NoTemplateHaskell #-}
{-# LANGUAGE NoGeneralizedNewtypeDeriving #-}
{-# LANGUAGE Safe #-}

module Clash.Crypto.ECDSA.Utils
 ( unsignedToSigned
 , signedToUnsigned
 ) where

import Clash.Prelude.Safe

unsignedToSigned ∷ ∀ len. KnownNat len ⇒ Unsigned len → Signed (len + 1)
unsignedToSigned = bitCoerce . zeroExtend

-- | `minBound` shouldn't be passed to `signedToUnsigned`, because
-- `abs minBound == minBound`
signedToUnsigned ∷ ∀ len. KnownNat len ⇒ Signed (len + 1) → Unsigned len
signedToUnsigned n = bitCoerce
  $ if result < 0
    then errorX "abs should not return a negative number"
    else result
 where
  result = truncateB $ abs n
