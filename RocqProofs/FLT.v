(* ssrbool import enables bool ~ Prop coercion *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat tuple seq div.
From Equations Require Import Equations.
From Bits Require Import bits.
From mathcomp Require Import zify.

Require Import Wf.

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

(* modulo *)
Equations moduloSeq {m : nat} {prf : m <> 0} (n : nat) : nat by wf n ltn2 :=
  moduloSeq (m := 0) _ with prf eq_refl := { | ! } ;
  moduloSeq 0 := 0 ; (* Should not be needed but makes everything simpler *)
  moduloSeq n :=
    if n < m then n
    else moduloSeq (m := m) (n - m)
.
Next Obligation.
  by rewrite /ltn2 ltn_subrL //=.
Qed.


Lemma moduloSeq1 : forall (bt_n bt_m : nat), bt_n < bt_m -> bt_n + (bt_m - bt_n) = bt_m.
  move=> bt_n bt_m Hineq.
  rewrite subnKC //.
  exact (ltnW Hineq).
Qed.

Inductive comparator (n m : nat) : Set :=
| Lt : n < m -> comparator n m
| Ge : m <= n -> comparator n m
.

Lemma compareHelper : forall n m, n <= m -> n.+1 <= m.+1.
  lia. 
Qed.

Lemma compareHelper2 : forall n m, n < m -> n.+1 < m.+1.
  lia. 
Qed.

Fixpoint compare_nat (n m : nat) : comparator n m :=
  match n, m with
  | 0, 0 => Ge (leqnn 0)
  | 0, m'.+1 => Lt (ltn0Sn m')
  | n'.+1, 0 => Ge (ltnW (ltn0Sn n'))
  | n'.+1, m'.+1 =>
    match compare_nat n' m' with
    | Lt H => Lt (compareHelper2 H)
    | Ge H => Ge (compareHelper H)
    end
  end.

Definition modulo_step {bt_n bt_m steps : nat} {m : BITS bt_m} {prf : 0 < bt_m} {prf2 : msb m = true}
                    {prf3 : bt_m <= bt_n} (n : BITS bt_n) : BITS bt_n :=
  let shiftedMod := shlBn (tuple.tcast (subnKC prf3) (zeroExtend (bt_n - bt_m) m)) steps in
  let newN       := if leB shiftedMod n then subB n shiftedMod else n in
  newN.

(* Taken from a more recent version of mathcomp *)
Lemma ltn_mull m1 m2 n1 n2 : 0 < n2 -> m1 < n1 -> m2 <= n2 -> m1 * m2 < n1 * n2.
  Proof.
    move=> n20 lt_mn1 le_mn2.
    rewrite (@leq_ltn_trans (m1 * n2)) ?leq_mul2l ?le_mn2 ?orbT//.
    by rewrite ltn_mul2r lt_mn1 n20.
Qed.

(* common to two files *)
Lemma toNat_shlB_zExtend : forall (bitlength extra : nat) (x : BITS bitlength) (shift : nat),
    1 <= bitlength -> shift <= extra ->
    toNat (shlBn (zeroExtend extra x) shift) = toNat x * 2 ^ shift.
  move=> bitlength extra x shift Hbl. move: shift.
  elim=> [|shift IHshift] leq_shift /=.
  - by rewrite expn0 muln1 toNat_zeroExtend.
  - rewrite shlB_asMul toNat_mulB toNat_fromNat.
    have Hextra: 1 <= extra by rewrite -(ltn_predK leq_shift).
    have Hblextra : 2 <= bitlength + extra by rewrite -addn1; apply (leq_add Hbl Hextra).
    have Hpower : 4 <= 2 ^ (bitlength + extra).
    rewrite [_ < _]/(_.+1 <= _) [4]/(2^2);  apply leq_pexp2l.
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

Lemma useful : forall a b, ~~ a <-> ~~ b -> a <-> b.
  move=> a b H.
  by split ; apply contraLR ; apply H.
Qed.

Lemma notmsbBound : forall (n : nat) (p : BITS n.+1), msb p <-> 2 ^ n <= toNat p.
  move=> n p.
  apply useful.
  rewrite -ltnNge.
  rewrite -eqtype.eqbF_neg.
  by apply msb0Bounded.
Qed.
Lemma msb_tcast :  forall n m (bs: BITS n)(H: n = m), msb (tcast H bs) = msb bs.
  move=> n m bs H.
  by case: m / H.
Qed.

Lemma shlBn_tcast :  forall n m s (bs: BITS n)(H: n = m), shlBn (tcast H bs) s = tcast H (shlBn bs s).
  move=> n m s bs H.
  by case: m / H.
Qed.

Lemma notmsbBound2 : forall (n : nat) (p : BITS n), 0 < n -> msb p <-> 2 ^ n.-1 <= toNat p.
  move=> n p Hn.
  rewrite -(toNat_tcast p (eq_sym (ltn_predK Hn))) //.
  rewrite -(msb_tcast p (eq_sym (ltn_predK Hn))).
  by apply notmsbBound.
Qed. 

Lemma zeroExtend_tcast2 :  forall n m z (bs: BITS n) (H: n + z = m + z),
    zeroExtend z (tcast (addnI (add_comm2 H)) bs) = tcast H (zeroExtend z bs).
  move=> n m z bs H.
  have H2 : n = m by exact (addnI (add_comm2 H)).
  case: m / H2 H.
  move=> H.
  by rewrite [in LHS]zeroExtend_tcast !tcast_id.
Qed.

Lemma zeroExtend_tcast3 : forall n m z (bs: BITS n) (H : n + z = m),
    shlBn (tuple.tcast H (zeroExtend z bs)) z = tuple.tcast H (shlBn (zeroExtend z bs) z).
  move=> n m z bs H.
  by case: m / H.
Qed.

Lemma zeroExtend_tcast4 : forall n m z s (bs: BITS n) (H : n + z = m), s <= z ->
    shlBn (tuple.tcast H (zeroExtend z bs)) s = tuple.tcast H (shlBn (zeroExtend z bs) s).
  move=> n m z s bs H H2.
  by case: m / H.
Qed. 

Lemma rewriteShift : forall (bt_n bt_m : nat) (m : BITS bt_m) prf3, 0 < bt_m ->
    toNat (shlBn (tuple.tcast (subnKC prf3) (zeroExtend (bt_n - bt_m) m)) (bt_n - bt_m)) = toNat m * 2 ^ (bt_n - bt_m).
  move=> bt_n bt_m m prf3 Hbtm.
  rewrite zeroExtend_tcast3.
  rewrite toNat_tcast.
  rewrite toNat_shlB_zExtend //=.
Qed.

Lemma rewriteShift2 : forall (bt_n bt_m steps : nat) (m : BITS bt_m) prf3, 0 < bt_m -> steps <= bt_n - bt_m ->
    toNat (shlBn (tuple.tcast (subnKC prf3) (zeroExtend (bt_n - bt_m) m)) steps) = toNat m * 2 ^ steps.
  move=> bt_n bt_m steps m prf3 Hbtm Hsteps.
  rewrite zeroExtend_tcast4 //.
  rewrite toNat_tcast.
  by rewrite toNat_shlB_zExtend //.
Qed.

Lemma mul_util : forall a b c d, 0 < c -> b <= d -> a < b * c -> a < d * c.
  move=> a b c d H0 H1 H2.
  apply (leq_ltn_trans2 (n := b * c)). exact H2.
  by rewrite leq_pmul2r //.
Qed.

Lemma mul_util2 : forall a b c d, 0 < c -> b < d -> a <= b * c -> a < d * c.
  move=> a b c d H0 H1 H2.
  apply (leq_ltn_trans (n := b * c)). apply H2.
  by rewrite ltn_pmul2r //.
Qed.

Lemma mul_util3 : forall a b c d, 0 < c -> b <= d -> a <= b * c -> a <= d * c.
  move=> a b c d H0 H1 H2.
  apply (leq_trans (n := b * c)). apply H2.
  by rewrite leq_pmul2r //.
Qed.
 
Lemma first_step_msb : forall (bt_n bt_m : nat) (m : BITS bt_m) prf prf2 prf3 (n : BITS bt_n),
    toNat
      (modulo_step (steps := bt_n - bt_m) (m := m) (prf := prf) (prf2 := prf2) (prf3 := prf3) n) <
      toNat m * 2 ^ (bt_n - bt_m).
  move=> bt_n bt_m m prf prf2 prf3 n.
  rewrite /modulo_step leB_nat rewriteShift //.
  case_eq (toNat m * 2 ^ (bt_n - bt_m) <= toNat n) ; move=> Hle.
  - rewrite toNat_subB. rewrite rewriteShift //=.
    rewrite ltn_subLR //.
    rewrite (leq_ltn_trans2 (n := 2 ^ bt_n)) //.
    apply toNatBounded. rewrite addnn -muln2 -mulnA -{3}(expn1 2) -expnD.
    rewrite (mul_util3 (b := 2 ^ bt_m.-1)) //.
    rewrite expn_gt0 //=.
    apply notmsbBound2. apply prf. apply prf2.
    rewrite -expnD.
    rewrite leq_exp2l //. lia. 
    by rewrite leB_nat rewriteShift //.
  - rewrite ltnNge. by apply/negPf.
Qed.

Lemma shlBn_id : forall bt_n (n : BITS bt_n), shlBn n 0 = n.
  auto.
Qed.

Lemma shlBn_shlB : forall bt_n s (n : BITS bt_n), shlB (shlBn n s) = shlBn n s.+1.
  auto.
Qed.

Lemma step_mod : forall (bt_n bt_m : nat) (m : BITS bt_m) prf prf2 prf3 (n : BITS bt_n) steps,
    steps <= bt_n - bt_m ->
    toNat
      (modulo_step (steps := steps) (m := m) (prf := prf) (prf2 := prf2) (prf3 := prf3) n)
    =
      toNat n %[mod toNat m].
  move=> bt_n bt_m m prf prf2 prf3 n.
  elim/nat_ind=> [|steps IHstep] Hsteps ; rewrite /modulo_step.
  - rewrite shlBn_id.
    rewrite leB_nat toNat_tcast toNat_zeroExtend.
    case_eq (toNat m <= toNat n) ; move=> Hle ; auto ; first last.
    + rewrite toNat_subB. rewrite toNat_tcast toNat_zeroExtend.
      rewrite -modnDr.
      by rewrite subnK //.
    + rewrite leB_nat. by rewrite toNat_tcast toNat_zeroExtend.
  - case_eq (leB (shlBn (tcast (subnKC prf3) (zeroExtend (bt_n - bt_m) m)) steps.+1) n) ;
      move=> HleB ; trivial.
    rewrite toNat_subB //.
    rewrite zeroExtend_tcast4 //. rewrite toNat_tcast.
    rewrite toNat_shlB_zExtend //.
    rewrite -(modnMDl (2 ^ steps.+1)).
    rewrite leB_nat in HleB. rewrite shlBn_tcast toNat_tcast in HleB. rewrite toNat_shlB_zExtend // in HleB.
    by rewrite mulnC subnKC //.
Qed.
    
Lemma next_step_msb : forall (bt_n bt_m steps : nat) (m : BITS bt_m) prf prf2 prf3 (n : BITS bt_n),
    steps <= bt_n - bt_m ->
    toNat n < toNat m * 2 ^ (steps + 1) ->
    toNat
      (modulo_step (steps := steps) (m := m) (prf := prf) (prf2 := prf2) (prf3 := prf3) n) <
      toNat m * 2 ^ steps.
  move=> bt_n bt_m steps m prf prf2 prf3 n Hsteps Hle.
  rewrite /modulo_step.
  rewrite leB_nat rewriteShift2 //.
  case_eq (toNat m * 2 ^ steps <= toNat n) ; move=> HleC.
  - rewrite toNat_subB. rewrite rewriteShift2 //=.
    rewrite ltn_subLR //.
    rewrite addnn -muln2 -mulnA -{2}(expn1 2) -expnD //.
    by rewrite leB_nat rewriteShift2 //.
  - by rewrite ltnNge ; apply/negPf.
Qed.

Fixpoint moduloSeq_CT_rec (steps : nat) {bt_n bt_m : nat} {m : BITS bt_m} {prf : 0 < bt_m}
  {prf2 : msb m = true} {prf3 : bt_m <= bt_n}
  (n : BITS bt_n) : BITS bt_n :=
  match steps with
  | 0 => modulo_step (steps := 0) (m := m) (prf := prf) (prf2 := prf2) (prf3 := prf3) n
  | S steps => moduloSeq_CT_rec steps (bt_m := bt_m) (prf := prf) (prf2 := prf2) (prf3 := prf3)
              (modulo_step (steps := steps.+1) (m := m) (prf := prf) (prf2 := prf2) (prf3 := prf3) n)
  end.

Lemma modulo_loop_LE : forall (bt_n bt_m : nat) (m : BITS bt_m) prf prf2 prf3 steps (n : BITS bt_n),
    steps <= bt_n - bt_m ->
    toNat n < toNat m * 2 ^ (steps + 1) ->
    toNat (moduloSeq_CT_rec (m := m) (prf := prf) (prf2 := prf2) (prf3 := prf3) steps n) < toNat m.
  move=> bt_n bt_m m prf prf2 prf3.
  elim/nat_ind=> [|steps IHsteps] n Hsteps Hlt.
  - by rewrite -(muln1 (toNat m)) -(expn0 2) ; apply next_step_msb.
  - rewrite /moduloSeq_CT_rec -/moduloSeq_CT_rec.
    apply IHsteps.
    + by rewrite ltnW //.
    + by rewrite addn1 ; apply next_step_msb. 
Qed.

Lemma modulo_loop_mod : forall (bt_n bt_m : nat) (m : BITS bt_m) prf prf2 prf3 steps (n : BITS bt_n),
    steps <= bt_n - bt_m ->
    toNat (moduloSeq_CT_rec (m := m) (prf := prf) (prf2 := prf2) (prf3 := prf3) steps n) = toNat n %[mod toNat m].
  move=> bt_n bt_m m prf prf2 prf3.
  elim/nat_ind=> [|steps IHsteps] n Hsteps ; rewrite /moduloSeq_CT_rec.
  - by apply step_mod. 
  - rewrite -/moduloSeq_CT_rec.
    rewrite -(step_mod _ _ _ n Hsteps).
    by apply IHsteps; rewrite ltnW //.
Qed.

Equations moduloSeq_CT {bt_n bt_m : nat} {m : BITS bt_m} {prf : 0 < bt_m}
  {prf2 : msb m = true} (n : BITS bt_n) : BITS bt_n :=
  moduloSeq_CT n with compare_nat bt_n bt_m => {
      moduloSeq_CT n (Lt Hlt) := n;
      moduloSeq_CT n (Ge Hgt) :=
        let new_n := moduloSeq_CT_rec (bt_n - bt_m) (bt_n := bt_n) (bt_m := bt_m) (prf := prf) (prf2 := prf2) (prf3 := Hgt) n in new_n
    }.

Lemma mod_between : forall n m, m <= n < m * 2 -> n - m = n %% m.
  move=> n m /andP[Hmn Hnm2].
  have Hbound: 0 <= n - m < m by apply/andP; split ; lia.
  have Hdecomp: n = 1 * m + (n - m) by rewrite mul1n addnC subnK // ; apply/ltnW ; apply Hmn. 
  - apply/eq_sym.
    rewrite [in LHS]Hdecomp mul1n modnDl.
    by apply modn_small.
Qed.

Lemma moduloSeq_is_modulo : forall m prf n, moduloSeq (m := m) (prf := prf) n = n %% m.
  move=> m prf n.
  funelim (moduloSeq n) ; rewrite -Heqcall //=.
  case_eq (n.+1 < n0.+1) ; move=> Heq.
  - by apply PeanoNat.Nat.eq_sym_iff ; apply modn_small ; apply Heq.
  - by rewrite H -modnDr subnK //= ; rewrite ltnNge Bool.negb_false_iff //= in Heq.
Qed.

Theorem moduloSeq_CT_is_modulo : forall (bt_n bt_m : nat) (n : BITS bt_n) (m : BITS bt_m) prf prf2, toNat (moduloSeq_CT (m := m) (prf2 := prf2) (bt_m := bt_m) (prf := prf) n) = toNat n %% toNat m.
  move=> bt_n bt_m n m prf prf2.
  funelim (moduloSeq_CT n) ; rewrite -Heqcall.
  - rewrite modn_small //.
    rewrite (leq_ltn_trans2 (n := 2 ^ bt_n)) //.
    + by apply toNatBounded.
    + rewrite (leq_trans (n := 2 ^ bt_m.-1)) //.
      * rewrite leq_exp2l //.
        by apply nat.leq_subn.
      * by apply notmsbBound2.
  - rewrite -[in LHS](modn_small (m := toNat _) (d := toNat m)) ; first last.
    + apply modulo_loop_LE. trivial.
      apply (leq_ltn_trans2 (n := 2 ^ bt_n)).
      * by apply toNatBounded.
      * apply (mul_util3 (b := 2 ^ bt_m.-1)).
        apply expn_gt0. by apply notmsbBound2. 
      * by rewrite -expnD leq_exp2l // ; lia.
    + by apply modulo_loop_mod.
Qed.
