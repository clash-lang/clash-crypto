From mathcomp Require Import ssreflect ssrnat tuple seq.

From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Lemma bits_nat_equiv_power  : forall l a (p : BITS l),
    foldr (fun (b : bool) e => e ^ 2 * (if b then a else 1)) 1 p = a ^ (toNat p).
  elim=> [| l IHl] a p.
  - by rewrite toNatNil (tuple0 p) /foldr //=.
  - case/tupleP: p => [b bs].
    rewrite /foldr //= ; rewrite toNatCons addnC.
    rewrite /foldr in IHl.
    rewrite IHl expnD -muln2 expnM.
    by case: b => //=.
Qed.
