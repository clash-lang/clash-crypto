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
  Variable bt_m : nat.
  Variable m    : BITS bt_m.
  Variable prf  : 0 < bt_m.
  Variable prf2 : msb m = true.
  Variable n : BITS bt_m.

  Section Definitions.
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
  End Definitions.

  Section Helpers.
    Lemma on_step : forall steps a,
        toNat (flt_step steps a) = (toNat a ^ 2) * toNat (if getBit (decB m) steps then n else fromNat 1) %% toNat m.
      move=> ?? ; rewrite /flt_step.
      do 2 rewrite moduloSeq_CT_resized_is_modulo toNat_fullmulB.
      by rewrite mulnn modnMml.
    Qed.
  End Helpers.
End FLT.

Section Lemmas.
  Variable bl : nat.

  Lemma getBit0 : forall (p : BITS bl.+1), msb p = getBit p bl.
    case/tupleP=> ??.
    rewrite /msb //= (last_nth false) /getBit.
    by rewrite {1}size_tuple.
  Qed.
  
  Lemma msb_high1 : forall (p : BITS (bl + 1)), singleBit (msb p) = high 1 p.
    move=> p ; apply allBitsEq ; case=> _ //.
    rewrite getBit_high add0n.
    have H2 : bl + 1 = bl.+1 by apply addn1.
    by rewrite H2 in p * ; rewrite -!getBit0.
  Qed.

  Lemma nat_of_bool_is_toNat : forall idx (p : BITS bl),
      idx < bl ->
      nat_of_bool (getBit p idx) = toNat (singleBit (getBit p idx)).
    by case: bl => [|?] ??? // ; rewrite toNatCons //= toNatNil ; lia.
  Qed.

  Lemma toNat_high_tcast : forall (n0 n1 : nat) (m : BITS bl.+1) (Hw : bl.+1 = n0 + bl) (He : bl.+1 = n1 + bl), toNat (high bl (tcast He m)) = toNat (high bl (tcast Hw m)).
    move=> n0 n1 ???.
    f_equal ; apply allBitsEq ; move=> ??.
    rewrite !getBit_high !getBit_tcast.
    by have -> : n0 = n1 by lia.
  Qed.

  Lemma mod_other : forall a b c d, a = b %[mod d] -> a * c = b * c %[mod d].
    by move=> ???? H ; rewrite -modnMm H modnMm.
  Qed.
  
  Lemma mod_simpl : forall a b c, (a %% b) ^ 2 * c = a ^ 2 * c %[mod b].
    by move=> ??? ; apply mod_other ; rewrite modnXm.
  Qed.
End Lemmas.

Lemma toNat_high_decomp : forall
    (bt_m idx : nat)
    (n : BITS bt_m)
    (H : bt_m = bt_m - idx.+1 + idx.+1)
    (H2 : bt_m = (bt_m - idx.+1).+1 + idx),
    toNat (high idx.+1 (tcast H n)) = toNat (high idx (tcast H2 n)) * 2 + getBit n (bt_m - idx.+1).
  case=> [|bt_m] // ; case=> [|idx] n ? H2 //.
  - rewrite toNatNil mul0n add0n.
    rewrite -msb_high1 msb_tcast getBit0.
    have -> : bt_m.+1 - 1 = bt_m by lia.
    by rewrite nat_of_bool_is_toNat.
  - rewrite (addnC (toNat _ * 2)) muln2 ; rewrite -toNat_joinlsb.
    f_equal ; apply allBitsEq.
    case=> [|i] _.
    + rewrite /joinlsb {2}/getBit.
      by rewrite getBit_high getBit_tcast.
    + have -> : getBit (joinlsb (high idx.+1 (tcast H2 n), getBit n (bt_m.+1 - idx.+2))) i.+1 = getBit (high idx.+1 (tcast H2 n)) i by rewrite /getBit /joinlsb.
      by rewrite !getBit_high !getBit_tcast ; f_equal ; lia.
Qed.

Theorem fltEq_steps :
  forall (bt_m steps o : nat) (n : BITS bt_m) (m : BITS bt_m) (prf : 0 < bt_m) (prf2 : msb m) (H : bt_m = o + steps.+1),
    steps.+1 < bt_m ->
    toNat (fltSeq_CT_rec prf prf2 n steps)
    = toNat n ^ toNat (high steps.+1 (tcast H (decB m))) %% toNat m.
  case=> [|bt_m] // ; case: bt_m => [|bt_m] //.
  elim=> [|steps IHsteps] o n m ?? H _.
  - rewrite on_step toNat_fromNat.
    have -> : (1 %% 2 ^ bt_m.+2) ^ 2 = 1 by
      rewrite modn_small -{1}(expn0 2) // ltn_exp2l.
    rewrite mul1n -msb_high1 -getBit0 msb_tcast.
    case: (msb (decB m)) => //.
    have -> : toNat (singleBit false) = 0 by [].
    rewrite expn0 toNat_fromNat.
    by have -> : (1 %% 2 ^ bt_m.+2) = 1 by
      rewrite modn_small -{1}(expn0 2) // ltn_exp2l.
  - rewrite on_step.
    have Hx : o = bt_m.+2 - steps.+2 by lia.
    rewrite Hx in H * ; rewrite (IHsteps o.+1) ; first lia ; last lia.
    rewrite Hx in H * ; move=> H0.
    rewrite (toNat_high_decomp (decB m) H (idx := steps.+1) _).
    have -> : toNat (if getBit (decB m) (bt_m.+2 - steps.+2) then n else # (1)) = toNat n ^ getBit (decB m) (bt_m.+2 - steps.+2).
    case: (getBit (decB m) (bt_m.+2 - steps.+2)) => //.
    by rewrite toNat_fromNat modn_small // -{1}(expn0 2) ltn_exp2l.
    by rewrite mod_simpl -expnM expnD.
Qed.

Theorem fltEq :
  forall (bt_m : nat) (n : BITS bt_m) (m : BITS bt_m) (prf : 0 < bt_m) (prf2 : msb m),
    toNat (fltSeq_CT prf prf2 n) = toNat n ^ (toNat (decB m)) %% toNat m.
  case=> [|bt_m] // ; case: bt_m => [|bt_m] n m ??.
  - have H : m = ones 1 by apply allBitsEq ; case => // ; rewrite -getBit0 getBit_ones.
    have {H} Hm : toNat m = 1 by rewrite H toNat_ones ; lia.
    rewrite Hm modn1 /fltSeq_CT.
    simp fltSeq_CT_rec ; rewrite /flt_step.
    by do 2 rewrite moduloSeq_CT_resized_is_modulo toNat_fullmulB ; lia.
  - rewrite /fltSeq_CT.
    have H0 : bt_m.+2 = bt_m.+2 - bt_m.+1 + bt_m.+1 by lia.
    have -> : bt_m.+2.-1 = bt_m.+1 by lia.
    simp fltSeq_CT_rec.
    rewrite on_step (fltEq_steps (o := bt_m.+2 - bt_m.+1) _ _ _ H0) ; last lia.
    rewrite mod_simpl -expnM.
    have -> : toNat (if getBit (decB m) (bt_m.+2 - bt_m.+2) then n else # (1)) =
               toNat n ^ getBit (decB m) (bt_m.+2 - bt_m.+2).
    case (getBit (decB m) (bt_m.+2 - bt_m.+2)) => //.
    by rewrite toNat_fromNat modn_small //= ; rewrite -{1}(expn0 2) // ; rewrite ltn_exp2l //.
  - have H1 : bt_m.+2 = (bt_m.+2 - bt_m.+2).+1 + bt_m.+1 by lia.
    have H2 : bt_m.+2 = bt_m.+2 - bt_m.+2 + bt_m.+2 by lia.
    rewrite (toNat_high_tcast _ H1) -expnD.
    rewrite -(toNat_high_decomp _ H2 H1).
    by have <- : decB m = high bt_m.+2 (tcast H2 (decB m))
      by apply allBitsEq ; move=> ?? ; rewrite getBit_high {3}subnn addn0 getBit_tcast.
Qed.
