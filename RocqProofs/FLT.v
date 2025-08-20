(*From mathcomp Require Import all_ssreflect all_algebra. *)
Require Import Coq.Init.Wf.
Require Import Stdlib.Arith.Arith_base.

Require Import Coq.Init.Peano.
Require Import Corelib.Program.Wf.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.PeanoNat.
Require Import Arith.
Require Import Stdlib.NArith.BinNat. 
Require Import Stdlib.Lists.List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Program Fixpoint nat_to_bits (n : nat) {measure n} : list bool :=
  match n with
  | O => cons false nil
  | S O => cons true nil
  | _ => Nat.odd n :: (nat_to_bits (Nat.div2 n))
  end.
Next Obligation.
  (*apply Nat.div_lt; lia.*)
  apply Nat.lt_div2.
  Search (_ = _ <-> _ = _).
  apply Nat.neq_0_lt_0.
  Search (_ <> _).
  apply Nat.neq_sym.
  apply H0.
Qed.

Search "rev".

Lemma ntb_nonzero (n : nat) : nat_to_bits (S (S n)) = Nat.odd (S (S n)) :: nat_to_bits (Nat.div2 (S (S n))).
  unfold nat_to_bits at 1.
  rewrite fix_sub_eq.
  simpl.
  fold nat_to_bits.
  reflexivity.
  intros a b c Heq.
  destruct a.
  reflexivity.
  induction a.
  trivial.
  f_equal. f_equal.
Qed.

Lemma pred_succ_comm n : 1 <= n -> pred (S n) = S (pred n).
  intro Hn.
  rewrite Nat.succ_pred_pos.
  rewrite <- Nat.pred_succ.
  reflexivity.
  apply Hn.
Qed.

Search (_ <= pred _).

Lemma bonjour n : 2 <= n -> pred (S (S (pred n))) = S (S (pred (pred n))).
  intro Hn.
  pose proof (Nat.le_le_pred 2 n Hn) as H2.
  simpl in H2.
  rewrite <- Nat.succ_pred_pos in H2.
  rewrite (pred_succ_comm H2).
  rewrite <- Nat.succ_pred_pos in H2.
  pose proof Hn as H3.
  simpl in H3.
  rewrite <- Nat.pred_succ in H3.
  Search (pred _ <= pred _).
  apply (Nat.pred_le_mono 2 n) in H3.
  simpl in H3.
  rewrite (pred_succ_comm H3).
  reflexivity.
  trivial.
  trivial.
Qed.
  
Lemma nat_to_bits_mul_false (n : nat) : 0 < n -> nat_to_bits (n * 2) = false::nat_to_bits n.
  intro Hn.
  Search (_ * _).
  pose proof (Nat.mul_le_mono_r 1 n 2 Hn).
  rewrite <- (Nat.succ_pred_pos (n * 2)).
  rewrite <- (Nat.pred_succ (S (pred (n * 2)))).
  Search (pred (S _)).
  Search (S (pred _)).
  rewrite bonjour.
  rewrite ntb_nonzero.
  Search (Nat.even _).
  rewrite Nat.succ_pred_pos.
  rewrite Nat.mul_comm.
  rewrite Nat.succ_pred_pos.
  rewrite Nat.odd_even.
  Search (Nat.div2).
  rewrite Nat.div2_even.
  reflexivity.
  Search (_ < _ * _).
  (* Try to refactor here. *)
  apply Nat.mul_pos_pos. apply Nat.lt_0_2.
  trivial. simpl in H.
  Search (_ <= _).
  pose proof (Nat.le_le_pred 2 (n * 2) H).
  simpl in H0.
  Search (_ <= _ -> _ < _).
  apply Nat.pred_le_mono in H.
  simpl in H.
  apply PeanoNat.le_lt_n_Sm in H.
  Search (S (pred _)).
  rewrite (Nat.succ_pred_pos (n * 2)) in H.
  Search (S _ < S _).
  apply PeanoNat.lt_S_n.
  Search (S (pred _)).
  rewrite (Nat.succ_pred_pos).
  apply H.
  trivial. trivial.
  trivial. trivial. simpl in H.
  Search (_ <= _ -> _ < _).
  apply PeanoNat.le_lt_n_Sm in H.
  Search (_ < _).
  apply PeanoNat.lt_S_n in H.
  Search (0 < 1).
  Search "lt_trans".
  apply (Nat.lt_trans _ _ _  Nat.lt_0_1 H).
Qed.

Lemma nat_to_bits_mul_true (n : nat) : 0 < n -> nat_to_bits (n * 2 + 1) = true::nat_to_bits n.
  intro Hn.
  Search (_ * _).
  pose proof (Nat.mul_le_mono_r 1 n 2 Hn).
  rewrite <- (Nat.succ_pred_pos (n * 2)).
  rewrite <- (Nat.pred_succ (S (pred (n * 2)))).
  Search (pred (S _)).
  Search (S (pred _)).
  rewrite bonjour.
  rewrite Nat.add_1_r.
  Search (_ + 1 = S _).
  rewrite ntb_nonzero.
  Search (Nat.even _).
  rewrite Nat.succ_pred_pos.
  rewrite Nat.mul_comm.
  rewrite Nat.succ_pred_pos.
  Search (2 * _).
  rewrite <- Nat.add_1_r.
  rewrite Nat.odd_odd.
  Search (Nat.div2).
  rewrite Nat.div2_odd'.
  reflexivity.
  Search (_ < _ * _).
  (* Try to refactor here. *)
  apply Nat.mul_pos_pos. apply Nat.lt_0_2.
  trivial. simpl in H.
  Search (_ <= _).
  pose proof (Nat.le_le_pred 2 (n * 2) H).
  simpl in H0.
  Search (_ <= _ -> _ < _).
  apply Nat.pred_le_mono in H.
  simpl in H.
  apply PeanoNat.le_lt_n_Sm in H.
  Search (S (pred _)).
  rewrite (Nat.succ_pred_pos (n * 2)) in H.
  Search (S _ < S _).
  apply PeanoNat.lt_S_n.
  Search (S (pred _)).
  rewrite (Nat.succ_pred_pos).
  apply H.
  trivial. trivial.
  trivial. trivial. simpl in H.
  Search (_ <= _ -> _ < _).
  apply PeanoNat.le_lt_n_Sm in H.
  Search (_ < _).
  apply PeanoNat.lt_S_n in H.
  Search (0 < 1).
  Search "lt_trans".
  apply (Nat.lt_trans _ _ _  Nat.lt_0_1 H).
Qed.

Import ListNotations.

Lemma singleton_list (A : Type) (a : A) (l : list A) : a :: l = [a] ++ l.
  trivial.
Qed.

Definition bits_to_nat (bl : list bool) : nat := fold_right (fun (b : bool) e => e * 2 + (if b then 1 else 0)) 0 bl.

Lemma bits_nat_equiv (n : nat) :
  bits_to_nat (nat_to_bits n) = n.
Proof.
  (* intro H0. *)
  unfold bits_to_nat.
  induction n using Nat.binary_induction.
  trivial.
  rewrite Nat.mul_comm.
  induction n.
  * trivial.
  *  rewrite nat_to_bits_mul_false.
  rewrite singleton_list.
  rewrite fold_right_app.
  simpl fold_right.
  rewrite <- plus_n_O.
  rewrite IHn.
  reflexivity.
  Search (0 < S _).
  apply Nat.lt_0_succ.
  * rewrite Nat.mul_comm.
  induction n.
  trivial.
  rewrite nat_to_bits_mul_true.
  rewrite singleton_list.
  rewrite fold_right_app.
  simpl fold_right.
  Search (_ + _ = _ + _).
  rewrite IHn.
  reflexivity.
  apply Nat.lt_0_succ.
Qed.

Definition bitlength (n : nat) : nat := List.length (nat_to_bits n).

Fixpoint pad {A : Type} (padding : nat) (val : A) (lst : list A) :=
  match padding with
  | O => lst
  | S n => val :: pad n val lst
  end.

Definition nat_to_bits_padded (bitlength : nat) (n : nat) : list bool :=
  let n_bits := nat_to_bits n in
  let n_bits_len := length n_bits in
  if n_bits_len <=? bitlength then pad (bitlength - n_bits_len) false n_bits
  else skipn (n_bits_len - bitlength) n_bits
.

Lemma pp1 (bl : list bool) : bl = [] -> false <> last bl true.
  intro.
  rewrite H.
  simpl last.
  Search (false <> true).
  apply diff_false_true.
Qed.
Lemma pp (bl : list bool) : false = last bl true -> bl <> [].
  Search "contra".
  intro.
  contradict H.
  apply pp1 in H. apply H.
Qed.
Program Fixpoint remove_trailing_z (bl : list bool) {measure (List.length bl)} :=
  match bl with
  | [] => []
  | _ =>
    match List.last bl true with
    | false => remove_trailing_z (List.removelast bl)
    | true => bl
    end
  end.
Next Obligation.
  pose proof (not_eq_sym n).
  pose proof (app_removelast_last (A := bool) (l := bl) false).
  apply H0 in H.
  rewrite H at 2.
  rewrite length_app.
  rewrite <- Nat.add_0_r at 1.
  apply Nat.add_lt_mono_l.
  simpl.
  apply Nat.lt_0_1.
Qed.
  
Lemma bits_without_trailing_z (bl : list bool) :
  bl <> [] ->
  bits_to_nat bl = bits_to_nat (remove_trailing_z bl).
  Search (_ :: _).
  intro Hineq.
  induction bl.
  trivial.
  unfold remove_trailing_z.
  rewrite fix_sub_eq.
  simpl.
  Search (_ :: _).
  fold remove_trailing_z.
  
  (* Remember nil_cons *)
Qed.
  
Lemma bits_nat_equiv_rev (bl : list bool) :
  nat_to_bits (bits_to_nat bl) = remove_trailing_z bl.
  

Lemma bits_nat_equiv_power a n :
  (fold_right (fun (b : bool) e => e ^ 2 * (if b then a else 1)) 1 (nat_to_bits n)) = a ^ n.
  induction n using Nat.binary_induction.
  trivial.
  rewrite Nat.mul_comm.
  induction n.
  trivial.
  rewrite nat_to_bits_mul_false.
  rewrite singleton_list.
  rewrite fold_right_app.
  rewrite IHn.
  unfold fold_right.
  Search (_ ^ _).
  rewrite Nat.pow_mul_r.
  Search (_ * 1).
  rewrite Nat.mul_1_r.
  reflexivity.
  apply Nat.lt_0_succ.
  trivial.
  rewrite Nat.mul_comm.
  induction n.
  simpl.
  rewrite Nat.mul_1_r.
  rewrite Nat.add_0_r.
  reflexivity.
  rewrite nat_to_bits_mul_true.
  rewrite singleton_list.
  rewrite fold_right_app.
  rewrite IHn.
  unfold fold_right.
  Search (_ ^ _).
  rewrite <- Nat.pow_mul_r.
  Search (_ ^ _).
  rewrite Nat.pow_add_r.
  Search (_ ^ 1).
  rewrite Nat.pow_1_r.
  reflexivity.
  apply Nat.lt_0_succ.
Qed.

Search "prime".

Require Import Stdlib.ZArith.Znumtheory.

