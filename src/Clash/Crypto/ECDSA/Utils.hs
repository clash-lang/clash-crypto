{-# LANGUAGE PatternSynonyms #-}

module Clash.Crypto.ECDSA.Utils
 ( ComputationState
 , pattern Working, pattern Finished
 , unsignedToSigned, signedToUnsigned)
where

import Clash.Prelude

type ComputationState a = Maybe a

{-# COMPLETE Working, Finished #-}
pattern Working :: a -> ComputationState a
pattern Working a = Just a

pattern Finished :: ComputationState a
pattern Finished = Nothing

unsignedToSigned :: forall len . KnownNat len => Unsigned len -> Signed (len + 1)
unsignedToSigned = bitCoerce . zeroExtend

-- | `minBound` shouldn't be passed to `signedToUnsigned`, because `abs minBounc == minBound`
signedToUnsigned :: forall len . KnownNat len => Signed (len + 1) -> Unsigned len
signedToUnsigned n =
  bitCoerce $
   if result < 0 then errorX "abs should not return a negative number" else result
 where
  result = truncateB $ abs n
