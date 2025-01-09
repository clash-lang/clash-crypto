{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.ECDSA.Lemmas where
import Clash.Prelude
import Data.Constraint (Dict (..))
import qualified GHC.TypeLits as P
import Unsafe.Coerce (unsafeCoerce)

lemma_mod :: forall len n m. (KnownNat len, KnownNat n, KnownNat m, n ~ m + 1, P.Mod len (2 ^ n) ~ 0) =>
 Dict (P.Mod (Div len 2) (2 ^ m) ~ 0)
lemma_mod = unsafeCoerce (Dict :: Dict (0 ~ 0))

lemma_mul_div :: forall len n. (KnownNat len, KnownNat n, 1 <= n) =>
 Dict (Div len n * n ~ len)
lemma_mul_div = unsafeCoerce (Dict :: Dict (0 ~ 0))

lemma_pow :: forall n. (KnownNat n) => Dict (1 <= 3 ^ n)
lemma_pow = unsafeCoerce (Dict :: Dict (0 <= 0))
