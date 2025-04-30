module Clash.Crypto.ECDSA.Utils where

import Clash.Prelude

-- | `minBound` shouldn't be passed to `signedToUnsigned`, because `abs minBounc == minBound`
signedToUnsigned :: forall len . KnownNat len => Signed (len + 1) -> Unsigned len
signedToUnsigned n =
  bitCoerce $
   if result < 0 then errorX "abs should not return a negative number" else result
 where
  result = truncateB $ abs n
