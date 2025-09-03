Require Import Coq.Init.Wf.
Require Import Coq.Program.Wf.
From Equations Require Import Equations.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssreflect.fintype.
From mathcomp Require Import zify.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Bits Require Import bits.

Search BITS.

(* TODO: Make bitlength a variable global to the section
   However, it needs to interact correctly with the karatsuba defintion. *)

Section Karatsuba.
  
  (* We need wellfoundedness in order to use `<` as a measure. *)  
  Section Well_founded_Nat.
    Variable A : Type.
    Variable f : A -> nat.

    Definition ltof (a b:A) := f a < f b.

    Lemma leq_ltn_trans2 n m p : m < n -> n <= p -> m < p.
      by move=> Hmn; apply: leq_trans.
    Qed.

    (* There are easier proofs given as an example of Equations. *)

    Theorem well_founded_ltof : well_founded ltof.
      assert (H : forall n (a:A), f a < n -> Acc ltof a).
      { intro n; induction n as [|n IHn].
        - by intros a Ha; absurd (f a < 0); auto.
        - intros a Ha. apply Acc_intro. unfold ltof at 1. intros b Hb.
          apply IHn.
          apply leq_ltn_trans2 with (n := f a).
          apply Hb. by [].
          
      }
      by intros a ; apply (H (S (f a))) ; apply ltnSn.
    Qed.

  End Well_founded_Nat.
  
  Definition ltn2 (a b:nat) := a < b.

  Lemma ltn_wf : well_founded ltn2.
    exact (well_founded_ltof (fun m => m)).
  Qed.

  Instance ltn_wf' : WellFounded ltn2 := ltn_wf.

  Lemma uphalf_half1 : forall (n : nat), n = uphalf n + half n.
    move=> n.
    rewrite uphalf_half.
    by rewrite -{1}(odd_double_half n) -addnn addnA.
  Qed.

  Lemma half_uphalf : forall (n : nat), n = half n + uphalf n.
    move=> n.
    rewrite uphalf_half.
    by rewrite -{1}(odd_double_half n) -addnn addnCA.
  Qed.
  
  Program Definition idSum {bitlength : nat} (x : BITS bitlength) : BITS (half bitlength + uphalf bitlength) :=
    x.
  Next Obligation.
    by apply half_uphalf.
  Qed.

  Program Definition sumId {bitlength : nat} (x : BITS (half bitlength + uphalf bitlength)) : BITS bitlength :=
    x.
  Next Obligation.
    by rewrite -half_uphalf.
  Qed.

  Definition kara_split2 {bitlength : nat} (x : BITS bitlength)
    : BITS (uphalf bitlength) * BITS (half bitlength) :=
    split2 (uphalf bitlength) (half bitlength) (idSum x).

  Program Definition reduceK {bitlength : nat} (x : BITS (bitlength./2 + (bitlength - bitlength./2 - bitlength./2))) : BITS (bitlength - bitlength./2) :=  x.
  Next Obligation.
    lia.
  Qed.

  Program Definition extendHalf {bitlength : nat} (x : BITS (half bitlength)) : BITS (uphalf bitlength) :=
    zeroExtend (odd bitlength) x.
  Next Obligation.
    by rewrite uphalf_half addnC.
  Qed.

  Lemma kObligation n : ltn2 (uphalf n).+1 n.+2.
    by rewrite /ltn2 ; lia.
  Qed.

  Lemma extendHalfUphalfPlusOne (bitlength : nat) : bitlength./2 + (odd bitlength + 1) = (uphalf bitlength + 1).
    by rewrite addnA uphalf_half [in RHS](addnC (odd _)).
  Qed.

  Lemma extendKaraHigh (bitlength :nat) : (uphalf bitlength).*2 + 2 = (uphalf bitlength + 1).*2.
    by rewrite -[in RHS]muln2 mulnDl ![in RHS]muln2 //.
  Qed.

  Lemma extendz0 (bitlength : nat) : ((bitlength./2).*2) + (((odd bitlength).*2) + 2) = (uphalf bitlength +1).*2.
    by rewrite uphalf_half addnC [in RHS]addnAC !doubleD //=.
  Qed.

  Equations karatsuba {bitlength : nat} {prf : bitlength <> 0} (x : BITS bitlength) (y: BITS bitlength) : BITS (bitlength.*2) by wf bitlength ltn2  :=
    karatsuba (bitlength := 0) _ _ with prf eq_refl := { | ! } ;
    karatsuba (bitlength := n.+4) x y :=
      let bitlength := n.+4 in (* Maybe there's a better way to expose bitlength after destructing it *)
      let (x_high, x_low) := kara_split2 x in
      let (y_high, y_low) := kara_split2 y in
      let x_sum := addB (zeroExtend 1 x_high) (tuple.tcast (extendHalfUphalfPlusOne bitlength) (zeroExtend (odd bitlength + 1) x_low)) in
      let y_sum := addB (zeroExtend 1 y_high) (tuple.tcast (extendHalfUphalfPlusOne bitlength) (zeroExtend (odd bitlength + 1) y_low)) in
      let z0 := tuple.tcast (extendz0 bitlength) (zeroExtend ((odd bitlength).*2 + 2) (karatsuba (bitlength := half bitlength) x_low y_low)) in
      let z2 := tuple.tcast (extendKaraHigh bitlength) (zeroExtend 2 (karatsuba (bitlength := uphalf bitlength) x_high y_high)) in
      let z3 := karatsuba (bitlength := uphalf bitlength + 1) x_sum y_sum in
      let z1 := subB (subB z3 z2) z0 in
      (tuple.tcast _ (
           (addB
              (shlBn (zeroExtend (bitlength./2.*2 - 2) z2) (bitlength./2.*2))
              (addB
                 (shlBn (zeroExtend (bitlength./2.*2 - 2) z1) (bitlength./2))
                 (zeroExtend (bitlength./2.*2 - 2) z0))))) ;
    karatsuba x y := fromNat (toNat x * toNat y)
  .
  Next Obligation.
    by rewrite /ltn2 ; lia.
  Qed.
  Next Obligation.
    by rewrite /ltn2 ; lia.
  Qed.
  Next Obligation.
    by rewrite /ltn2 ; lia.
  Qed.
  Next Obligation.
    lia.
  Qed.

  Definition computePair {bitlength : nat} (x : BITS bitlength) : nat :=
    let (x1, x0) := kara_split2 x in
    (2 ^ half bitlength) * toNat x1 + toNat x0
  .

  Lemma kara_s : forall (bitlength :nat) (x : BITS bitlength),
      kara_split2 x = (high (uphalf bitlength) (idSum x), low (half bitlength) (idSum x)).
    move=> bitlength x.
    by rewrite /kara_split2 /split2.
  Qed.

  Lemma pair_equal : forall (bitlength : nat) (x : BITS bitlength), toNat x = computePair x.
    move=> bitlength x.
    rewrite /computePair /kara_split2 /= mulnC -(toNatCat (high _ _) (low _ _)).
    by rewrite -split2eta toNat_tcast.
  Qed.

  Lemma kara_sum : forall (A x0 x1 y0 y1 : nat),
      (x1 * A + x0) * (y1 * A + y0) = x1 * y1 * A ^2 + (x1 * y0 + x0 * y1) * A + x0 * y0.
    Unset Printing Parentheses.
    lia.
  Qed.

  Lemma z1_sum : forall (x0 x1 y0 y1 : nat),
      x0 * y1 + x1 * y0 = (x0 + x1) * (y0 + y1) - x0 * y0 - x1 * y1.
    lia.
  Qed.

  (* Taken from a more recent version of mathcomp *)
  Lemma ltn_mull m1 m2 n1 n2 : 0 < n2 -> m1 < n1 -> m2 <= n2 -> m1 * m2 < n1 * n2.
  Proof.
    move=> n20 lt_mn1 le_mn2.
    rewrite (@leq_ltn_trans (m1 * n2)) ?leq_mul2l ?le_mn2 ?orbT//.
    by rewrite ltn_mul2r lt_mn1 n20.
  Qed.

  Lemma half_sum n : n./2 = n - uphalf n.
    lia.
  Qed.

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
      rewrite [_ < _]/(_.+1 <= _) [4]/(2^2). apply leq_pexp2l. by []. exact Hblextra.
      rewrite (IHshift (ltnW leq_shift)).
      rewrite !div.modn_small. by rewrite -mulnA -expnSr.
      have Hbidule: 2 < 3 by [].
      apply (ltn_trans Hbidule Hpower).
      rewrite -mulnA -expnSr.
      rewrite expnD.
      apply ltn_mull.
      rewrite -{1}(exp0n (n := extra) Hextra).
      apply ltn_exp2r. exact Hextra.
      apply toNatBounded.
      apply leq_pexp2l. by []. exact leq_shift.
      apply (ltn_trans) with (n := 3). by []. exact Hpower.
  Qed.

  Lemma n_half_odd n : n./2.*2 = n - odd n.
    lia.
  Qed.

  Lemma rewritetwos n x y : x * y * 2 ^ (n./2.*2) * 2 * 2 ^ 3 = x * y * 2 ^ (n./2.*2 + 4).
    by rewrite [in RHS]expnD [in RHS]expnS mulnA mulnA.
  Qed.

  Lemma rewriteStuff xl xh yl yh : (xh + xl) * (yh + yl) - xh * yh = xh * yl + xl * yh + xl * yl.
    lia.
  Qed.

  Lemma rewritepower n : 2 ^ (n./2.*2 + 4) = (2 ^ (n./2 +2)) ^ 2.
    set (my_term := ((n./2).*2 + 2.*2)%Nrec).
    assert (H_eq : my_term = (n./2).*2 + 2.*2) by reflexivity.
    rewrite -H_eq H_eq. (* Replace my_term everywhere *)
    clear H_eq my_term. (* Clean up *)
    rewrite -doubleD -muln2.
    by rewrite expnM.
  Qed.

  Lemma rewriteterm2 x n : x * 2 ^ n./2 * 2 * 2 = x * 2 ^ (n./2 + 2).
    by rewrite expnD -mulnn mulnA mulnA.
  Qed.
  
  Lemma ltn_add m1 m2 n1 n2 : m1 < n1 -> m2 <= n2 -> m1 + m2 < n1 + n2.
    move=> lt_mn1 lt_mn2.
    rewrite (@leq_ltn_trans2 (m2 + n1)) //. rewrite addnC ?ltn_add2l //.
    by rewrite addnC ?leq_add2l.
  Qed.

  Lemma big_ineq n (y : BITS n.+4) :
    toNat (high (uphalf n).+2 (tuple.behead_tuple (tuple.behead_tuple (idSum y)))) + div.modn (toNat (idSum y)) (2 ^ n./2.+2) < 2 ^ ((uphalf n).+2 + 1).
    rewrite expnD expn1 muln2 -addnn.
    apply ltn_add.
    - apply toNatBounded.
    - apply leq_trans with (n := 2 ^ n./2.+2) ; last (apply leq_pexp2l ; first by []).
      + apply ltnW.
      + apply div.ltn_pmod.
        rewrite -(addn2 (n./2)).
        rewrite expnD -{1}(muln0 0).
        by apply ltn_mul ; last 1 [ by rewrite expn_gt0 | by [] ].
    - rewrite -(leq_add2r (n./2)) -(addn2 (uphalf n)) -addnA addnCA (addnC (uphalf n)) -half_uphalf.
      rewrite (addnC 2).
      rewrite addnC -addn2 addnA addnn n_half_odd.
      rewrite addnBAC ; last (by rewrite -div.modn2 ; apply div.leq_mod).
      by apply leq_subr.
  Qed.

  Lemma simplmod x n :
    div.modn ((div.modn x (2 ^ n)).*2) (2 ^ n) = (div.modn (x.*2) (2 ^ n)).
    rewrite -muln2 div.muln_modl.
    rewrite div.modn_dvdm muln2 //. 
    rewrite -muln2 mulnC -expnS.
    by apply div.dvdn_exp2l.
  Qed.

  Lemma simplN n : (((uphalf n).+2 + 1).*2 + ((n./2.+2).*2 - 2)) = n.*2 + 8.
    lia.
  Qed.

  Lemma simplPow x y n : ((((x * y * 2 ^ ((n./2).*2)%Nrec).*2).*2).*2).*2 = x * y * (2 ^ (n./2.+2)) ^ 2.
    set (my_term := ((n./2).*2)%Nrec).
    assert (H_eq : my_term = (n./2).*2) by reflexivity.
    rewrite H_eq. (* Replace my_term everywhere *)
    clear H_eq my_term. (* Clean up *)
    rewrite -!muln2 -![in LHS]mulnA mulnn -!expnS -expnD.
    have -> : 4 = 2.*2 by lia.
    rewrite muln2 -doubleD addn2 -muln2.
    by rewrite expnM mulnA.
  Qed.

  Lemma simplPow2 x n : ((x * 2 ^ n./2).*2).*2 = x * 2 ^ n./2.+2.
    by rewrite -!muln2 -!mulnA mulnn -expnD addn2.
  Qed.
  
  Lemma katarsuba_mul : forall (bitlength : nat) (x : BITS bitlength) (y : BITS bitlength) (prf : bitlength <> 0),
      toNat (karatsuba (prf := prf) x y) = toNat x * toNat y.
    move=> bitlength x y prf.
    funelim (karatsuba x y).
    - rewrite -Heqcall.
      rewrite toNat_fromNatBounded //.
      by rewrite -[2 ^ (1.*2)]/(2 * 2); apply ltn_mul; do 2! apply toNatBounded.
    - rewrite -Heqcall toNat_fromNatBounded // -muln2 expnM -mulnn.
      by apply ltn_mul; do 2! apply toNatBounded.
    - rewrite -Heqcall toNat_fromNatBounded // -muln2 expnM -mulnn.
      by apply ltn_mul; do 2! apply toNatBounded.
    - rewrite -Heqcall.
      rewrite toNat_tcast.
      rewrite !toNat_addB !toNat_shlB.
      rewrite !toNat_shlB_zExtend.
      rewrite !toNat_tcast.
      rewrite !toNat_zeroExtend !toNat_tcast !toNat_zeroExtend.
      rewrite !toNat_subB.
      rewrite !toNat_tcast !toNat_zeroExtend.
      rewrite !H0 ; first 2 [ exact (zero (uphalf n.+4)) | exact (zero n.+4./2) | exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | reflexivity ].
      rewrite !H1 ; first 2 [ exact (zero (uphalf n.+4)) | exact (zero n.+4./2) | exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | reflexivity ].
      rewrite !H ; first 2 [ exact (zero (uphalf n.+4)) | exact (zero n.+4./2) | exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | reflexivity ].
      rewrite !toNat_addB !toNat_zeroExtend !toNat_tcast !toNat_zeroExtend.
      rewrite !simplmod.
      rewrite !div.modnDmr !div.modnDml.
      rewrite -(addnn (div.modn _ _)) -(addnn (div.modn _ _ + div.modn _ _)).
      rewrite -addnA -addnA.
      rewrite div.modnDml.
      rewrite addnC -addnA.
      rewrite div.modnDml.
      rewrite addnCA -addnA - addnA.
      rewrite div.modnDml addnC.
      rewrite -addnA div.modnDml addnC -addnA -addnA - addnA.
      rewrite div.modnDml addnC. rewrite !addnn.
      rewrite -!toNat_fullmulB.
      rewrite !(div.modn_small (m := (toNat _ + toNat _))) ; last first.
      + by rewrite toNat_low ; apply big_ineq.
      + by rewrite toNat_low ; apply big_ineq.
      rewrite div.modn_small.
      rewrite !toNat_fullmulB.
      (* to remove the Nrec scope *)
      set (my_term := ((n./2).*2)%Nrec).
      assert (H_eq : my_term = (n./2).*2) by reflexivity.
      rewrite H_eq. (* Replace my_term everywhere *)
      clear H_eq my_term. (* Clean up *)
      rewrite -addnCAC -!muln2 -!mulnA !mulnn. 
      rewrite -!expnS -!expnD addnACl (addnC ((toNat (joinlsb _) * _))) addnA.
      rewrite -(addn2 2) addnn muln2 -doubleD -muln2 expnM.
      rewrite -z1_sum.
      rewrite ![in RHS]pair_equal /computePair //=.
      rewrite ![in RHS](mulnC (2 ^ _)).
      rewrite [in RHS]kara_sum.
      by rewrite addn2 mulnA //.
    - (* big ineq *)
      rewrite !toNat_fullmulB.
      rewrite -z1_sum simplN simplPow simplPow2.
      rewrite -addnA addnC -addnA addnA -kara_sum.
      have ->: n.*2 + 8 = n.+4.*2 by lia.
      rewrite -muln2 expnM -mulnn.
      have Hother: n.+4 = n./2.+2 + (uphalf n).+2 by lia.
      apply ltn_mul ; do 2! [rewrite -toNatCat {5}Hother ; apply toNatBounded].
    (* End of big proof *)
    - rewrite leB_nat.
      rewrite toNat_tcast toNat_zeroExtend.
      rewrite H0 ; first 2 [ exact (zero (uphalf n.+4)) | exact (zero n.+4./2) | exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | reflexivity ].
      rewrite H1 ; first 2 [ exact (zero (uphalf n.+4)) | exact (zero n.+4./2) | exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | reflexivity ].
      rewrite !toNat_addB.
      rewrite !toNat_tcast !toNat_zeroExtend.
      apply leq_mul.
      rewrite div.modn_small.
      apply leq_addr.
      rewrite expnD expn1 muln2 -addnn.
      apply ltn_add.
      apply toNatBounded.
      apply leq_trans with (n := 2 ^ (half n).+2).
      rewrite toNat_low.
      apply ltnW.
      apply div.ltn_pmod.
      rewrite -(addn2 (n./2)).
      rewrite expnD -{1}(muln0 0).
      apply ltn_mul.
      by rewrite expn_gt0. by [].
      apply leq_pexp2l. by [].
      rewrite -(leq_add2r (n./2)) -(addn2 (uphalf n)) -addnA addnCA (addnC (uphalf n)) -half_uphalf.
      rewrite (addnC 2).
      rewrite addnC -addn2 addnA addnn n_half_odd.
      rewrite addnBAC.
      by apply leq_subr.
      rewrite -div.modn2.
      by apply div.leq_mod.
      rewrite div.modn_small.
      apply leq_addr.
      rewrite toNat_low.
      by apply big_ineq.
    - rewrite leB_nat.
      rewrite toNat_tcast toNat_zeroExtend toNat_subB.
      rewrite toNat_tcast toNat_zeroExtend.
      rewrite H ; first 2 [ exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | reflexivity ].
      rewrite H1 ; first 2 [ exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | reflexivity ].
      rewrite H0 ; first 2 [ exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | reflexivity ].
      rewrite !toNat_addB.
      rewrite !div.modn_small ; first last.
      + by rewrite toNat_tcast ; rewrite !toNat_zeroExtend ; rewrite toNat_low ; apply big_ineq.
      + by rewrite toNat_tcast ; rewrite !toNat_zeroExtend ; rewrite toNat_low ; apply big_ineq.        
      rewrite !toNat_tcast.
      rewrite !toNat_zeroExtend.
      rewrite rewriteStuff.
      rewrite addnCAC -addnA.
      by apply leq_addr.
      rewrite leB_nat.
      rewrite H1 ; first 2 [ exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | reflexivity ].
      rewrite !toNat_addB.
      rewrite !div.modn_small ; first last.
      + by rewrite toNat_tcast ; rewrite !toNat_zeroExtend ; rewrite toNat_low ; apply big_ineq.
      + by rewrite toNat_tcast ; rewrite !toNat_zeroExtend ; rewrite toNat_low ; apply big_ineq.        

      rewrite !toNat_tcast.
      rewrite !toNat_zeroExtend.
      rewrite H0 ; first 2 [ exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | exact (zero (uphalf n.+4)) |  exact (zero n.+4./2) | reflexivity ].

      by rewrite mulnDl mulnDr -addnA leq_addr.
      by [].
      lia.
      by [].
      set (my_term := ((n./2).*2)%Nrec).
      assert (H_eq : my_term = (n./2).*2) by reflexivity.
      rewrite H_eq. (* Replace my_term everywhere *)
      clear H_eq my_term. (* Clean up *)
      lia.
  Qed.

End Karatsuba.
