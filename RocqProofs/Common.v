(* ssrbool import enables bool ~ Prop coercion *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat tuple seq div.
From Equations Require Import Equations.
From Bits Require Import bits.
From mathcomp Require Import zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma leq_ltn_trans2 n m p : m < n -> n <= p -> m < p.
  by move=> Hmn; apply: leq_trans.
Qed.

(* Taken from a more recent version of mathcomp *)
Lemma ltn_mull m1 m2 n1 n2 : 0 < n2 -> m1 < n1 -> m2 <= n2 -> m1 * m2 < n1 * n2.
  Proof.
    move=> n20 lt_mn1 le_mn2.
    rewrite (@leq_ltn_trans (m1 * n2)) ?leq_mul2l ?le_mn2 ?orbT//.
    by rewrite ltn_mul2r lt_mn1 n20.
Qed.

Lemma toNat_shlB_zExtend : forall (bitlength extra : nat) (x : BITS bitlength) (shift : nat),
    1 <= bitlength -> shift <= extra ->
    toNat (shlBn (zeroExtend extra x) shift) = toNat x * 2 ^ shift.
  move=> bitlength extra x shift Hbl.
  elim: shift => [|shift IHshift] leq_shift /=.
  - by rewrite expn0 muln1 toNat_zeroExtend.
  - rewrite shlB_asMul toNat_mulB toNat_fromNat.
    have Hextra: 1 <= extra by rewrite -(ltn_predK leq_shift).
    have Hblextra : 2 <= bitlength + extra by rewrite -addn1; apply (leq_add Hbl Hextra).
    have Hpower : 4 <= 2 ^ (bitlength + extra).
    rewrite [_ < _]/(_.+1 <= _) [4]/(2^2); apply leq_pexp2l.
    + by [].
    + exact Hblextra.
      rewrite (IHshift (ltnW leq_shift)).
      rewrite !div.modn_small.
    + by rewrite -mulnA -expnSr.
    + have H2lt3: 2 < 3 by [].
      exact (ltn_trans H2lt3 Hpower).
    + rewrite -mulnA -expnSr.
      rewrite expnD.
      apply ltn_mull.
      * rewrite -{1}(exp0n (n := extra) Hextra).
        apply ltn_exp2r. exact Hextra.
      * by apply toNatBounded.
      * apply leq_pexp2l. by []. exact leq_shift.
      * apply (ltn_trans) with (n := 3). by []. exact Hpower.
Qed.

Lemma zeroExtend_tcast :  forall n m z (bs: BITS n) (H: n = m), zeroExtend z (tcast H bs) = tcast (f_equal (fun x => x + z) H) (zeroExtend z bs).
  move=> n m z bs H.
  by case: m / H.
Qed.

Lemma add_comm2 : forall n m z, n + z = m + z -> z + n = z + m.
  lia.
Qed.

Lemma contra_equiv : forall a b, ~~ a <-> ~~ b -> a <-> b.
  move=> a b H.
  by split ; apply contraLR ; apply H.
Qed.


Lemma msb_tcast : forall n m (bs: BITS n)(H: n = m), msb (tcast H bs) = msb bs.
  move=> n m bs H.
  by case: m / H.
Qed.

Lemma shlBn_tcast : forall n m s (bs: BITS n)(H: n = m), shlBn (tcast H bs) s = tcast H (shlBn bs s).
  move=> n m s bs H.
  by case: m / H.
Qed.

Lemma zeroExtend_tcast_eq : forall n m z (bs: BITS n) (H : n + z = m),
    shlBn (tuple.tcast H (zeroExtend z bs)) z = tuple.tcast H (shlBn (zeroExtend z bs) z).
  move=> n m z bs H.
  by case: m / H.
Qed.

Lemma zeroExtend_tcast_less : forall n m z s (bs: BITS n) (H : n + z = m), s <= z ->
    shlBn (tuple.tcast H (zeroExtend z bs)) s = tuple.tcast H (shlBn (zeroExtend z bs) s).
  move=> n m z s bs H H2.
  by case: m / H.
Qed.

Lemma leq_mulL : forall a b c d, 0 < c -> b <= d -> a <= b * c -> a <= d * c.
  move=> a b c d H0 H1 H2.
  apply (leq_trans (n := b * c)). apply H2.
  by rewrite leq_pmul2r //.
Qed.

Lemma shlBn_id : forall bt_n (n : BITS bt_n), shlBn n 0 = n.
  by [].
Qed.

Lemma shlBn_shlB : forall bt_n s (n : BITS bt_n), shlB (shlBn n s) = shlBn n s.+1.
  by [].
Qed.
