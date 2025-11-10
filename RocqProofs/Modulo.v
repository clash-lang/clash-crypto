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

Section Modulo.
  Variable bt_n bt_m : nat.
  Variable n : BITS bt_n.
  Variable m : BITS bt_m.
  Variable prf  : 0 < bt_m.
  Variable prf2 : msb m = true.

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
  
  Lemma moduloSeq_is_modulo : forall m0 prf0 n0, moduloSeq (prf := prf0) (m := m0) n0 = n0 %% m0.
    move=> ?? n0.
    funelim (moduloSeq n0) ; rewrite -Heqcall //.
    case_eq (n1.+1 < n0.+1) ; move=> Heq.
    - by apply PeanoNat.Nat.eq_sym_iff ; apply modn_small ; apply Heq.
    - by rewrite H -modnDr subnK // ; rewrite ltnNge Bool.negb_false_iff // in Heq.
  Qed.

  (* This implementation reproduces the inner workings of the mealy machine behind
   computeModuloUnsigned.
   In order to keep the proof simple, it emulates the circuit if it received only
   one computable input and only None afterwards. This enables us to prove that the
   computation is in constant-time.
   A more general proof, proving that not only the first input will be computed in
   that amount of time will be provided later. *)

  Section BiggerThan.
    Variable prf3 : bt_m <= bt_n.
    Definition modulo_step {steps : nat} (n : BITS bt_n) : BITS bt_n :=
      let shiftedMod := shlBn (tuple.tcast (subnKC prf3) (zeroExtend (bt_n - bt_m) m)) steps in
      let newN       := if leB shiftedMod n then subB n shiftedMod else n in
      newN.
    
    Fixpoint moduloSeq_CT_rec (steps : nat) (n : BITS bt_n) : BITS bt_n :=
      match steps with
      | 0 => modulo_step (steps := 0) n
      | S steps => moduloSeq_CT_rec steps
                    (modulo_step (steps := steps.+1) n)
      end.

    Lemma rewriteShift :
      toNat (shlBn (tuple.tcast (subnKC prf3) (zeroExtend (bt_n - bt_m) m)) (bt_n - bt_m)) = toNat m * 2 ^ (bt_n - bt_m).
      rewrite zeroExtend_tcast_eq.
      rewrite toNat_tcast.
      by rewrite toNat_shlB_zExtend //.
    Qed.

    Lemma rewriteShift2 : forall (steps : nat),
        steps <= bt_n - bt_m ->
        toNat (shlBn (tuple.tcast (subnKC prf3) (zeroExtend (bt_n - bt_m) m)) steps)
        =
          toNat m * 2 ^ steps.
      move=> ??.
      rewrite zeroExtend_tcast_less //.
      rewrite toNat_tcast.
      by rewrite toNat_shlB_zExtend //.
    Qed.

    Lemma step_mod : forall steps n0,
        steps <= bt_n - bt_m ->
        toNat (modulo_step (steps := steps) n0) = toNat n0 %[mod toNat m].
      case=> [|steps] n0 ? ; rewrite /modulo_step.
      - rewrite shlBn_id.
        rewrite leB_nat toNat_tcast toNat_zeroExtend.
        case_eq (toNat m <= toNat n0) ; move=> Hle ; auto ; first last.
        + rewrite toNat_subB. rewrite toNat_tcast toNat_zeroExtend.
          rewrite -modnDr.
          by rewrite subnK //.
        + rewrite leB_nat. by rewrite toNat_tcast toNat_zeroExtend.
      - case_eq (leB (shlBn (tcast (subnKC prf3) (zeroExtend (bt_n - bt_m) m)) steps.+1) n0) ;
          move=> HleB //.
        rewrite toNat_subB //.
        rewrite zeroExtend_tcast_less //. rewrite toNat_tcast.
        rewrite toNat_shlB_zExtend //.
        rewrite -(modnMDl (2 ^ steps.+1)).
        rewrite leB_nat in HleB ;rewrite shlBn_tcast toNat_tcast in HleB ;
          rewrite toNat_shlB_zExtend // in HleB.
        by rewrite mulnC subnKC //.
    Qed. 
    

    Lemma next_step_ltn : forall (n0 : BITS bt_n) (steps : nat),
        steps <= bt_n - bt_m ->
        toNat n0 < toNat m * 2 ^ (steps + 1) ->
        toNat (modulo_step (steps := steps) n0) < toNat m * 2 ^ steps.
      move=> n0 steps ??.
      rewrite /modulo_step leB_nat rewriteShift2 //.
      case_eq (toNat m * 2 ^ steps <= toNat n0) ; move=> ?.
      - rewrite toNat_subB. rewrite rewriteShift2 //=.
        rewrite ltn_subLR //.
        rewrite addnn -muln2 -mulnA -{2}(expn1 2) -expnD //.
        by rewrite leB_nat rewriteShift2 //.
      - by rewrite ltnNge ; apply/negPf.
    Qed.

    

    Lemma modulo_loop_LE : forall steps (n0 : BITS bt_n),
        steps <= bt_n - bt_m ->
        toNat n0 < toNat m * 2 ^ (steps + 1) ->
        toNat (moduloSeq_CT_rec steps n0) < toNat m.
      elim/nat_ind=> [|? IHsteps] n0 ?? ; simp moduloSeq_CT_rec.
      - by rewrite -(muln1 (toNat m)) -(expn0 2) ; apply next_step_ltn.
      - apply IHsteps.
        + by rewrite ltnW //.
        + by rewrite addn1 ; apply next_step_ltn.
    Qed.

    Lemma modulo_loop_mod : forall steps n0,
        steps <= bt_n - bt_m ->
        toNat (moduloSeq_CT_rec steps n0) = toNat n0 %[mod toNat m].
      elim/nat_ind=> [|? IHsteps] n0 Hsteps ; simp moduloSeq_CT_rec.
      - by apply step_mod.
      - by rewrite -(step_mod n0 Hsteps) ; apply IHsteps ; rewrite ltnW //.
    Qed.

  End BiggerThan.
  
  Lemma notmsbBound : forall (n : nat) (p : BITS n.+1), msb p <-> 2 ^ n <= toNat p.
    move=> ??.
    apply contra_equiv.
    rewrite -ltnNge.
    rewrite -eqtype.eqbF_neg.
    by apply msb0Bounded.
  Qed.

  Lemma notmsbBound2 : forall (x : nat) (p : BITS x), 0 < x -> msb p <-> 2 ^ x.-1 <= toNat p.
    move=> ? p Hn.
    rewrite -(toNat_tcast p (eq_sym (ltn_predK Hn))) //.
    rewrite -(msb_tcast p (eq_sym (ltn_predK Hn))).
    by apply notmsbBound.
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
  About injective.

  Equations moduloSeq_CT (n : BITS bt_n) : BITS bt_n :=
    moduloSeq_CT n with compare_nat bt_n bt_m => {
        moduloSeq_CT n (Lt Hlt) := n;
        moduloSeq_CT n (Ge Hgt) :=
          let new_n := moduloSeq_CT_rec Hgt (bt_n - bt_m) n in new_n
      }.
  
  Equations moduloSeq_CT_resized (n : BITS bt_n) : BITS bt_m :=
    moduloSeq_CT_resized n with compare_nat bt_n bt_m => {
        moduloSeq_CT_resized n (Lt Hlt) := tcast (subnKC (ltnW Hlt)) (zeroExtend (bt_m - bt_n) n);
        moduloSeq_CT_resized n (Ge Hgt) :=
          let new_n := moduloSeq_CT n in
          low bt_m (tcast (eq_sym (subnKC Hgt)) new_n)
      }.

  Lemma mod_between : forall n0 m0, m0 <= n0 < m0 * 2 -> n0 - m0 = n0 %% m0.
    move=> n0 m0 /andP[Hmn ?].
    have Hbound: 0 <= n0 - m0 < m0 by apply/andP; split ; lia.
    have Hdecomp: n0 = 1 * m0 + (n0 - m0) by rewrite mul1n addnC subnK // ; apply/ltnW ; apply Hmn.
    by apply/eq_sym ; rewrite [in LHS]Hdecomp mul1n modnDl ; apply modn_small.
  Qed.

  Theorem moduloSeq_CT_is_modulo : forall (v : BITS bt_n), toNat (moduloSeq_CT v) = toNat v %% toNat m.
    move=> ?.
    funelim (moduloSeq_CT _).
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

  Lemma x : forall a, 0 <> a -> 0 < a.
    lia.
  Qed.
  
  Theorem moduloSeq_CT_resized_is_modulo : forall (v : BITS bt_n), toNat (moduloSeq_CT_resized v) = toNat v %% toNat m.
    move=> ?.
    funelim (moduloSeq_CT_resized _).
    - rewrite toNat_tcast.
      rewrite toNat_zeroExtend. apply/eq_sym.
      apply modn_small.
      rewrite (leq_ltn_trans2 (n := 2 ^ bt_n)) //.
      + by apply toNatBounded.
      + rewrite (leq_trans (n := 2 ^ bt_m.-1)) //.
        * rewrite leq_exp2l //.
          by apply nat.leq_subn.
        * by apply notmsbBound2.
    - rewrite toNat_low. rewrite toNat_tcast. rewrite moduloSeq_CT_is_modulo.
      rewrite modn_small //.
      rewrite (leq_ltn_trans2 (n := toNat m)) //.
      + rewrite ltn_mod.
        apply x.
        rewrite -(toNat_zero bt_m).
        move=> H2.
        have H3 : zero bt_m = m by apply toNat_inj.
        have H4 : msb m = false by rewrite -H3; apply msb_zero.
        by rewrite prf2 // in H4.
      + apply ltnW.
        by apply toNatBounded.
  Qed.
End Modulo.
