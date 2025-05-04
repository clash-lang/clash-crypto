{-|
Module      : Clash.Crypto.ECDSA.Lemmas
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Some useful lemmas used in clash-crypto.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}

module Clash.Crypto.ECDSA.Lemmas where

import Clash.Prelude
import Data.Constraint (Dict (..))
import Unsafe.Coerce (unsafeCoerce)
import Clash.Crypto.ECDSA.Modulo (ModSize)

lemma_pow :: forall n. Dict (1 <= 3 ^ n)
lemma_pow = unsafeCoerce (Dict :: Dict (0 <= 0))

lemma_modSize :: forall n. 1 <= n => Dict (1 <= ModSize n)
lemma_modSize = unsafeCoerce (Dict :: Dict (0 <= 0))
