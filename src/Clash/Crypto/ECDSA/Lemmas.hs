{-|
Module      : Clash.Crypto.ECDSA.Lemmas
Copyright   : Copyright © 2025 QBayLogic B.V.
Maintainer  : QBayLogic B.V.
Stability   : experimental
Portability : POSIX

Some useful lemmas used in clash-crypto.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -fplugin=GHC.TypeNats.Proof.Plugin #-}

module Clash.Crypto.ECDSA.Lemmas (lemmaModSize, LemmaLowIsLess) where

import Clash.Prelude
import Data.Constraint (Dict (..))
import Unsafe.Coerce (unsafeCoerce)
import Clash.Crypto.ECDSA.Modulo (ModSize)
import GHC.TypeNats.Proof (QED)

lemmaModSize :: forall n. 1 <= n => Dict (1 <= ModSize n)
lemmaModSize = unsafeCoerce (Dict :: Dict (0 <= 0))

instance (LemmaLowIsLess n)
class (n `Div` 2 <= n) => LemmaLowIsLess n

{-/ Preamble (Coq):
Require Import Nat.
Require Import Arith Lia.
/-}

{-/ Proof (Coq): LemmaLowIsLess
  intro n.
  rewrite <- Nat.div2_div.
  apply Nat.le_div2_diag_l.
/-}

instance LemmaLowIsLess n => QED (LemmaLowIsLess n)

