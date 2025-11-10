(* ssrbool import enables bool ~ Prop coercion *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat tuple seq div.
From Equations Require Import Equations.
From Bits Require Import bits.
From mathcomp Require Import zify.

Require Import Wf.
Require Import Common.
Require Import Modulo.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FLT.
  Section Defs. 
    Variable bt_m : nat.
    Variable m    : BITS bt_m.
    Variable prf  : 0 < bt_m.
    Variable prf2 : msb m = true.
    Variable n : BITS bt_m.
    Variable prf_mod : ltB n m. (* TODO: Check if it is useful *)

    Definition flt_step (index : nat) (accum : BITS bt_m) : BITS bt_m :=
      let v1 := moduloSeq_CT_resized prf prf2 (fullmulB accum accum) in
      moduloSeq_CT_resized prf prf2 (fullmulB v1 (if getBit (decB m) index then n else fromNat 1)).

    (* starting from the LSB of the high part *)
    Equations fltSeq_CT_rec (steps : nat) : BITS bt_m :=
      fltSeq_CT_rec 0 := flt_step (bt_m - 1) #1 ;
      fltSeq_CT_rec s.+1 := flt_step (bt_m - s.+2) (fltSeq_CT_rec s)
    .
    
    Definition fltSeq_CT : BITS bt_m :=
      fltSeq_CT_rec bt_m.-1.
  End Defs.

  Lemma on_step : forall (steps bt_m : nat) (n m : BITS bt_m) (prf : 0 < bt_m) (prf2 : msb m) a,
      toNat (flt_step prf prf2 n steps a) = (toNat a ^ 2) * toNat (if getBit (decB m) steps then n else fromNat 1) %% toNat m.
    move=> steps bt_m n m prf prf2 a.
    rewrite /flt_step.
    rewrite moduloSeq_CT_resized_is_modulo.
    rewrite toNat_fullmulB.
    rewrite moduloSeq_CT_resized_is_modulo.
    rewrite toNat_fullmulB.
    rewrite mulnn.
    by rewrite modnMml.
  Qed.

  Lemma getBit0 : forall bt_m (m : BITS bt_m.+1), msb m = getBit m bt_m.
    move=> bt_m.
    case/tupleP=> m ms.
    rewrite /msb //=. rewrite (last_nth false). rewrite /getBit.
    by rewrite {1}size_tuple.
  Qed.

  Lemma msb_high1 : forall bt_m (m : BITS (bt_m + 1)), singleBit (msb m) = high 1 m.
    move=> bt_m m.
    apply allBitsEq.
    case=> // ; move=> _.
    rewrite getBit_high add0n.
    have H2 : bt_m + 1 = bt_m.+1 by lia.
    rewrite H2 in m *.
    by rewrite -!getBit0 //.
  Qed.

  Lemma auxa : forall bt_m idx (n : BITS bt_m),
      idx < bt_m ->
      nat_of_bool (getBit n idx) = toNat (singleBit (getBit n idx)).
    case=> [|?] ???.  
    - by []. 
    - by rewrite toNatCons //= toNatNil ; lia.
  Qed.

  Lemma aux :
    forall bt_m idx (n : BITS bt_m)
      (H : bt_m = bt_m - idx.+1 + idx.+1)
      (H2 : bt_m = (bt_m - idx.+1).+1 + idx),
      idx < bt_m ->
      toNat (high idx.+1 (tcast H n)) = toNat (high idx (tcast H2 n)) * 2 + getBit n (bt_m - idx.+1).
    elim=> [|bt_m _] //.
    elim=> [|idx IHidx] ; move=> n H H2 Hineq //=.
    - rewrite toNatNil. rewrite mul0n add0n.
      rewrite -msb_high1.
      rewrite msb_tcast.
      rewrite getBit0.
      have -> : bt_m.+1 - 1 = bt_m by lia.
      by rewrite auxa.
    - rewrite (addnC (toNat _ * 2)) muln2. rewrite -toNat_joinlsb.
      f_equal.
      apply allBitsEq.
      elim=> [|i IHi] ; move=> Hi.
      + rewrite /joinlsb {2}/getBit //=.
        rewrite getBit_high.
        by rewrite getBit_tcast.
      + have -> : getBit (joinlsb (high idx.+1 (tcast H2 n), getBit n (bt_m.+1 - idx.+2))) i.+1 = getBit (high idx.+1 (tcast H2 n)) i by rewrite /getBit /joinlsb //=.
        rewrite !getBit_high.
        rewrite !getBit_tcast.
        f_equal.
        lia.
  Qed.

  Lemma mod_other : forall a b c d, a = b %[mod d] -> a * c = b * c %[mod d].
    by move=> ???? H ; rewrite -modnMm H modnMm.
  Qed.

  Lemma mod_simpl : forall a b c, (a %% b) ^ 2 * c = a ^ 2 * c %[mod b].
    by move=> ??? ; apply mod_other ;rewrite modnXm.
  Qed.
  
  Lemma fltEq1 :
    forall (bt_m steps o : nat) (n : BITS bt_m) (m : BITS bt_m) (prf : 0 < bt_m) (prf2 : msb m) (H : steps.+1 < bt_m) (H2 : bt_m = o + steps.+1),
      toNat (fltSeq_CT_rec prf prf2 n steps)
      = toNat n ^ toNat (high steps.+1 (tcast H2 (decB m))) %% toNat m.
    elim=> [|bt_m _] //.
    elim: bt_m => [|bt_m IHbtm] //.
    - elim=> [|steps IHsteps] ; move=> o n m prf prf2 H H2.
      + rewrite on_step.
        rewrite toNat_fromNat .
        have -> : (1 %% 2 ^ bt_m.+2) ^ 2 = 1 by rewrite modn_small ; rewrite -{1}(expn0 2) // ; rewrite ltn_exp2l //.
        rewrite mul1n.
        rewrite -msb_high1.
        rewrite -getBit0.
        rewrite msb_tcast.
        case_eq (msb (decB m)) ; move=> _.
        * by [].
        * have -> : toNat (singleBit false) = 0 by [].
          rewrite expn0 toNat_fromNat.
          by have -> : (1 %% 2 ^ bt_m.+2) = 1 by rewrite modn_small ; rewrite -{1}(expn0 2) // ; rewrite ltn_exp2l //.
      + rewrite on_step.
        have Hx : o = bt_m.+2 - steps.+2 by lia.
        rewrite Hx in H2 *.        
        rewrite (IHsteps o.+1). lia.
        move=> H0.
        have Hm : (bt_m.+2 - steps.+2).+1 + steps.+1 = bt_m.+2 - steps.+1 + steps.+1 by lia.
        rewrite Hx in H2 H0 *.
        have H3 : bt_m.+2 = bt_m.+2 - steps.+1 + steps.+1 by lia.
        rewrite (aux (decB m) H2 (idx := steps.+1) H0) //.
        have -> : toNat (if getBit (decB m) (bt_m.+2 - steps.+2) then n else # (1)) = toNat n ^ getBit (decB m) (bt_m.+2 - steps.+2).
        case_eq (getBit (decB m) (bt_m.+2 - steps.+2)) ; move=> ?.
        by [].
        rewrite toNat_fromNat modn_small //=. rewrite -{1}(expn0 2) // ; rewrite ltn_exp2l //.
        rewrite mod_simpl.
        rewrite -expnM.
        by rewrite expnD.
        lia.
        lia.
  Qed.

  Lemma fltEq :
    forall (bt_m : nat) (n : BITS bt_m) (m : BITS bt_m) (prf : 0 < bt_m) (prf2 : msb m),
      toNat (fltSeq_CT prf prf2 n) = toNat n ^ (toNat (decB m)) %% toNat m.
    elim=> [|bt_m _] //.
    elim: bt_m => [|bt_m _]; move=> n m prf prf2.
    - have H : m = ones 1.
      apply allBitsEq.
      move=> i Hi.
      case: i => // in Hi *.
      rewrite -getBit0. by rewrite getBit_ones.
      have Hm : toNat m = 1.
      rewrite H.
      rewrite toNat_ones. lia.
      rewrite Hm modn1.
      rewrite /fltSeq_CT.
      simp fltSeq_CT_rec.
      rewrite /flt_step.
      rewrite moduloSeq_CT_resized_is_modulo.
      rewrite toNat_fullmulB.
      rewrite moduloSeq_CT_resized_is_modulo.
      rewrite toNat_fullmulB toNat_fromNat.
      have -> : 1 %% 2 ^ 1 = 1 by lia.
      rewrite mul1n modnMml mul1n Hm.
      by rewrite modn1.
    - rewrite /fltSeq_CT.
      have -> : bt_m.+2.-1 = bt_m.+1 by lia.
      simp fltSeq_CT_rec.
      have H3 : bt_m.+2 = bt_m.+2 - bt_m.+1 + bt_m.+1 by lia.
      rewrite on_step.
      rewrite (fltEq1 (o := bt_m.+2 - bt_m.+1) _ _ _ _ H3).
      rewrite mod_simpl.
      rewrite -expnM.
      have -> : toNat (if getBit (decB m) (bt_m.+2 - bt_m.+2) then n else # (1)) =
                 toNat n ^ getBit (decB m) (bt_m.+2 - bt_m.+2).
      case_eq (getBit (decB m) (bt_m.+2 - bt_m.+2)) ; move=> _.
      by [].
      rewrite toNat_fromNat modn_small //=. rewrite -{1}(expn0 2) // ; rewrite ltn_exp2l //.
      have H4 : bt_m.+2 = (bt_m.+2 - bt_m.+2).+1 + bt_m.+1 by lia.
      (* TODO: Move outside as a lemma *)
      have H5 : forall Hw He, toNat (high bt_m.+1 (tcast He (decB m))) = toNat (high bt_m.+1 (tcast Hw (decB m))).
      + move=> n0 n1 Hw He.
        have Hq : n0 = n1 by lia.
        f_equal.
        apply allBitsEq ;move=> i Hi.
        rewrite !getBit_high.
        rewrite !getBit_tcast. 
        by rewrite Hq.
      rewrite (H5 _ _ H4).
      rewrite -expnD.
      have H6 : bt_m.+2 = bt_m.+2 - bt_m.+2 + bt_m.+2 by lia.
      rewrite -(aux (idx := bt_m.+1) (decB m) H6 H4).
      have <- : decB m = high bt_m.+2 (tcast H6 (decB m)).
      apply allBitsEq ; move=> ??.
      rewrite getBit_high.
      rewrite {3}subnn addn0.
      by rewrite getBit_tcast.
      reflexivity.
      lia.
      lia.
  Qed.
End FLT.
