(* ssrbool import enables bool ~ Prop coercion *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat tuple seq div.
From Equations Require Import Equations.
From Bits Require Import bits.
From mathcomp Require Import zify.

Require Import Wf.
Require Import Common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A loose proof for the inner workings of fltCtmi.
   It will be followed by a Signal-based coinductive proof later. *)

Lemma bits_nat_equiv_power  : forall l a (p : BITS l),
    foldr (fun (b : bool) e => e ^ 2 * (if b then a else 1)) 1 p = a ^ (toNat p).
  elim=> [| l IHl] a p.
  - by rewrite toNatNil (tuple0 p) /foldr //=.
  - case/tupleP: p => [b bs].
    rewrite /foldr //= ; rewrite toNatCons addnC.
    rewrite /foldr in IHl.
    rewrite IHl expnD -muln2 expnM.
    by case: b => //.
Qed.

(* A very basic variable time sequential implementation for unsigned modulo *)
Equations moduloSeq {m : nat} {prf : m <> 0} (n : nat) : nat by wf n ltn2 :=
  moduloSeq (m := 0) _ with prf eq_refl := { | ! } ;
  moduloSeq 0 := 0 ; (* Should not be needed but makes everything simpler *)
  moduloSeq n :=
    if n < m then n
    else moduloSeq (m := m) (n - m)
.
Next Obligation.
  by rewrite /ltn2 ltn_subrL //.
Qed.

(* This implementation reproduces the inner workings of the mealy machine behind
   computeModuloUnsigned.
   In order to keep the proof simple, it emulates the circuit if it received only
   one computable input and only None afterwards. This enables us to prove that the
   computation is in constant-time.
   A more general proof, proving that not only the first input will be computed in
   that amount of time will be provided later. *)
Definition modulo_step {bt_n bt_m steps : nat} {m : BITS bt_m} {prf : 0 < bt_m} {prf2 : msb m = true}
  {prf3 : bt_m <= bt_n} (n : BITS bt_n) : BITS bt_n :=
  let shiftedMod := shlBn (tuple.tcast (subnKC prf3) (zeroExtend (bt_n - bt_m) m)) steps in
  let newN       := if leB shiftedMod n then subB n shiftedMod else n in
  newN.

Fixpoint moduloSeq_CT_rec (steps : nat) {bt_n bt_m : nat} {m : BITS bt_m} {prf : 0 < bt_m}
  {prf2 : msb m = true} {prf3 : bt_m <= bt_n}
  (n : BITS bt_n) : BITS bt_n :=
  match steps with
  | 0 => modulo_step (steps := 0) (m := m) (prf := prf) (prf2 := prf2) (prf3 := prf3) n
  | S steps => moduloSeq_CT_rec steps (bt_m := bt_m) (prf := prf) (prf2 := prf2) (prf3 := prf3)
                (modulo_step (steps := steps.+1) (m := m) (prf := prf) (prf2 := prf2) (prf3 := prf3) n)
  end.

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

Equations moduloSeq_CT {bt_n bt_m : nat} {m : BITS bt_m} {prf : 0 < bt_m}
  {prf2 : msb m = true} (n : BITS bt_n) : BITS bt_n :=
  moduloSeq_CT n with compare_nat bt_n bt_m => {
      moduloSeq_CT n (Lt Hlt) := n;
      moduloSeq_CT n (Ge Hgt) :=
        let new_n := moduloSeq_CT_rec (bt_n - bt_m) (bt_n := bt_n) (bt_m := bt_m) (prf := prf) (prf2 := prf2) (prf3 := Hgt) n in new_n
    }.

Lemma notmsbBound : forall (n : nat) (p : BITS n.+1), msb p <-> 2 ^ n <= toNat p.
  move=> n p.
  apply contra_equiv.
  rewrite -ltnNge.
  rewrite -eqtype.eqbF_neg.
  by apply msb0Bounded.
Qed.

Lemma notmsbBound2 : forall (n : nat) (p : BITS n), 0 < n -> msb p <-> 2 ^ n.-1 <= toNat p.
  move=> n p Hn.
  rewrite -(toNat_tcast p (eq_sym (ltn_predK Hn))) //.
  rewrite -(msb_tcast p (eq_sym (ltn_predK Hn))).
  by apply notmsbBound.
Qed. 

Lemma rewriteShift : forall (bt_n bt_m : nat) (m : BITS bt_m) prf3, 0 < bt_m ->
                                                             toNat (shlBn (tuple.tcast (subnKC prf3) (zeroExtend (bt_n - bt_m) m)) (bt_n - bt_m)) = toNat m * 2 ^ (bt_n - bt_m).
  move=> bt_n bt_m m prf3 Hbtm.
  rewrite zeroExtend_tcast_eq.
  rewrite toNat_tcast.
  by rewrite toNat_shlB_zExtend //=.
Qed.

Lemma rewriteShift2 : forall (bt_n bt_m steps : nat) (m : BITS bt_m) prf3, 0 < bt_m -> steps <= bt_n - bt_m ->
                                                                    toNat (shlBn (tuple.tcast (subnKC prf3) (zeroExtend (bt_n - bt_m) m)) steps) = toNat m * 2 ^ steps.
  move=> bt_n bt_m steps m prf3 Hbtm Hsteps.
  rewrite zeroExtend_tcast_less //.
  rewrite toNat_tcast.
  by rewrite toNat_shlB_zExtend //.
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
      move=> HleB //.
    rewrite toNat_subB //.
    rewrite zeroExtend_tcast_less //. rewrite toNat_tcast.
    rewrite toNat_shlB_zExtend //.
    rewrite -(modnMDl (2 ^ steps.+1)).
    rewrite leB_nat in HleB ;rewrite shlBn_tcast toNat_tcast in HleB ;
      rewrite toNat_shlB_zExtend // in HleB.
    by rewrite mulnC subnKC //.
Qed.

Lemma next_step_ltn : forall (bt_n bt_m steps : nat) (m : BITS bt_m) prf prf2 prf3 (n : BITS bt_n),
    steps <= bt_n - bt_m ->
    toNat n < toNat m * 2 ^ (steps + 1) ->
    toNat
      (modulo_step (steps := steps) (m := m) (prf := prf) (prf2 := prf2) (prf3 := prf3) n) <
      toNat m * 2 ^ steps.
  move=> bt_n bt_m steps m prf prf2 prf3 n Hsteps Hle.
  rewrite /modulo_step leB_nat rewriteShift2 //.
  case_eq (toNat m * 2 ^ steps <= toNat n) ; move=> HleC.
  - rewrite toNat_subB. rewrite rewriteShift2 //=.
    rewrite ltn_subLR //.
    rewrite addnn -muln2 -mulnA -{2}(expn1 2) -expnD //.
    by rewrite leB_nat rewriteShift2 //.
  - by rewrite ltnNge ; apply/negPf.
Qed.

Lemma modulo_loop_LE : forall (bt_n bt_m : nat) (m : BITS bt_m) prf prf2 prf3 steps (n : BITS bt_n),
    steps <= bt_n - bt_m ->
    toNat n < toNat m * 2 ^ (steps + 1) ->
    toNat (moduloSeq_CT_rec (m := m) (prf := prf) (prf2 := prf2) (prf3 := prf3) steps n) < toNat m.
  move=> bt_n bt_m m prf prf2 prf3.
  elim/nat_ind=> [|steps IHsteps] n Hsteps Hlt.
  - by rewrite -(muln1 (toNat m)) -(expn0 2) ; apply next_step_ltn.
  - rewrite /moduloSeq_CT_rec -/moduloSeq_CT_rec.
    apply IHsteps.
    + by rewrite ltnW //.
    + by rewrite addn1 ; apply next_step_ltn.
Qed.

Lemma modulo_loop_mod : forall (bt_n bt_m : nat) (m : BITS bt_m) prf prf2 prf3 steps (n : BITS bt_n),
    steps <= bt_n - bt_m ->
    toNat (moduloSeq_CT_rec (m := m) (prf := prf) (prf2 := prf2) (prf3 := prf3) steps n) = toNat n %[mod toNat m].
  move=> bt_n bt_m m prf prf2 prf3.
  elim/nat_ind=> [|steps IHsteps] n Hsteps ; rewrite /moduloSeq_CT_rec.
  - by apply step_mod. 
  - rewrite -/moduloSeq_CT_rec -(step_mod _ _ _ n Hsteps).
    by apply IHsteps; rewrite ltnW //.
Qed.

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
    + apply modulo_loop_LE. by [].
      apply (leq_ltn_trans2 (n := 2 ^ bt_n)).
      * by apply toNatBounded.
      * apply (leq_mulL (b := 2 ^ bt_m.-1)).
        apply expn_gt0. by apply notmsbBound2. 
      * by rewrite -expnD leq_exp2l // ; lia.
    + by apply modulo_loop_mod.
Qed.
