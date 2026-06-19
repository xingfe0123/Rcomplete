Require Import Reals.
Require Import Lra.
Require Import Classical_Prop.
Open Scope R_scope.

(* Test if each can be proven in standard Coq Reals *)

Lemma test_exp_positive : forall t : R, 0 < exp t.
Proof.
  intros.
  apply exp_pos.
Qed.

Lemma test_divide : forall (a b c : R), 0 < c -> a * c <= b -> a <= b / c.
Proof.
  intros a b c Hc Hab.
  apply Rmult_le_reg_r with (r := /c).
  - apply Rinv_pos; assumption.
  - rewrite Rmult_comm.
    rewrite Rmult_assoc.
    rewrite Rinv_l; try lra.
    rewrite Rmult_1_r.
    assumption.
Qed.

Lemma test_div_is_exp_neg : forall (delta t c : R), 0 < exp (delta * t) -> c / exp (delta * t) = c * exp (- delta * t).
Proof.
  intros.
  unfold Rdiv.
  rewrite Rinv_mult_simpl_l.
  - rewrite exp_neg.
    reflexivity.
  - apply exp_pos.
Qed.

Print Assumptions test_exp_positive.
Print Assumptions test_divide.
Print Assumptions test_div_is_exp_neg.
