{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.ECDSA.Lemmas where
import Clash.Prelude
import Data.Constraint (Dict (..))
import Unsafe.Coerce (unsafeCoerce)

lemma_mod :: forall len n m. (n ~ m + 1, len `Mod` (2 ^ n) ~ 0) =>
 Dict ((Div len 2) `Mod` (2 ^ m) ~ 0)
lemma_mod = unsafeCoerce (Dict :: Dict (0 ~ 0))

lemma_mul_div :: forall len n. (1 <= n, len `Mod` n ~ 0) =>
 Dict (Div len n * n ~ len)
lemma_mul_div = unsafeCoerce (Dict :: Dict (0 ~ 0))

lemma_pow :: forall n. Dict (1 <= 3 ^ n)
lemma_pow = unsafeCoerce (Dict :: Dict (0 <= 0))
