module Clash.Crypto.ECDSA.Utils
 ( unsignedToSigned
 , signedToUnsigned
 ) where

import Clash.Prelude

unsignedToSigned ∷ ∀ len. KnownNat len ⇒ Unsigned len → Signed (len + 1)
unsignedToSigned = bitCoerce . zeroExtend

-- | `minBound` shouldn't be passed to `signedToUnsigned`, because
-- `abs minBound == minBound`
-- Warning: We can't shave a bit off Signed in this direction because Signed's `minBound`
-- is actually too big for the smaller Unsigned.
signedToUnsigned ∷ ∀ len. KnownNat len ⇒ Signed len → Unsigned len
signedToUnsigned n = truncateB . bitCoerce
  $ if result < 0
    then errorX "abs should not return a negative number"
    else result
 where
  result = abs $ extend @_ @_ @1 n
