Require Import Reals.
Require Import Rbasic_fun.
Require Import Coq.Program.Equality.
Require Import Vector.
Open Scope R_scope.

Fixpoint vr_distance {n : nat} : t R n -> t R n -> R :=
  match n with
  | 0 => fun _ _ => 0
  | S n' =>
      fun x y =>
        Rabs (Vector.hd x - Vector.hd y) +
        vr_distance (Vector.tl x) (Vector.tl y)
  end.

Lemma vr_distance_nonneg : forall n (x y : t R n), 0 <= vr_distance x y.
Proof.
  induction n; intros; simpl.
  - apply Rle_refl.
  - apply Rplus_le_le_0_compat; [apply Rabs_pos | apply IHn].
Qed.

Lemma vr_distance_symm : forall n (x y : t R n), vr_distance x y = vr_distance y x.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - f_equal.
    + assert (H: Vector.hd x - Vector.hd y = -(Vector.hd y - Vector.hd x)) by lra.
      rewrite H, Rabs_Ropp. reflexivity.
    + apply IHn.
Qed.

Lemma abs_zero_iff: forall a, Rabs a = 0 -> a = 0.
Proof.
  intros.
  lra.
Qed.
