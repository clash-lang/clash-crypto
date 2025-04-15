{-# LANGUAGE AllowAmbiguousTypes #-}
module Clash.Crypto.ECDSA.Utils where

import Clash.Prelude

signedToUnsigned :: forall len . KnownNat len => Signed (len + 1) -> Unsigned len
signedToUnsigned = bitCoerce . truncateB . abs

groupMaybes :: Maybe a -> Maybe b -> Maybe (a,b)
groupMaybes mA mB = do
 a <- mA
 b <- mB
 return (a,b)

groupMaybes3 :: Maybe a -> Maybe a -> Maybe a -> Maybe (a,a,a)
groupMaybes3 a b c = do
 a' <- a
 b' <- b
 c' <- c
 return (a',b',c')
