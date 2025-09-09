Require Import Coq.Init.Wf.
Require Import Coq.Program.Wf.
From Equations Require Import Equations.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
