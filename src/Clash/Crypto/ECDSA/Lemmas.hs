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

module Clash.Crypto.ECDSA.Lemmas (lemmaModSize, LemmaPow) where

import Clash.Prelude
import Data.Constraint (Dict (..))
import Unsafe.Coerce (unsafeCoerce)
import Clash.Crypto.ECDSA.Modulo (ModSize)
import GHC.TypeNats.Proof (QED)

lemmaModSize :: forall n. 1 <= n => Dict (1 <= ModSize n)
lemmaModSize = unsafeCoerce (Dict :: Dict (0 <= 0))

instance (LemmaPow n)
class (1 <= 3 ^ n) => LemmaPow n


{-/ Preamble (Coq):
Require Import Nat.
Require Import Arith Lia.
/-}

{-/ Proof (Coq): LemmaPow
 intros n.
 induction n.
 trivial.
 rewrite Nat.pow_succ_r.
 rewrite <- (Nat.mul_1_l) at 1.
 apply (Nat.mul_le_mono).
 rewrite <- Nat.add_1_r at 2.
 apply Nat.le_1_succ.
 apply IHn.
 apply (Nat.le_0_l n).
/-}

instance LemmaPow n => QED (LemmaPow n)

