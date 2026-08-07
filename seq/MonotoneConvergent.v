From Stdlib Require Import Reals RIneq Ranalysis.
From Stdlib Require Import Rfunctions.
From Stdlib Require Import Rseries.
From Stdlib Require Import SeqProp.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Compare_dec.

Open Scope R_scope.

(******************************************************************************)
(* 单调序列定义                                                                *)
(******************************************************************************)

Definition increasing (f : nat -> R) : Prop :=
  forall n, f n <= f (S n).

Definition decreasing (f : nat -> R) : Prop :=
  forall n, f (S n) <= f n.

Definition monotone (f : nat -> R) : Prop :=
  increasing f \/ decreasing f.

(******************************************************************************)
(* 有界序列定义                                                                *)
(******************************************************************************)

Definition bounded_above (f : nat -> R) : Prop :=
  exists M : R, forall n, f n <= M.

Definition bounded_below (f : nat -> R) : Prop :=
  exists m : R, forall n, m <= f n.

Definition bounded_seq_R (f : nat -> R) : Prop :=
  bounded_above f /\ bounded_below f.

(******************************************************************************)
(* 收敛定义                                                                    *)
(******************************************************************************)

Definition convergent_R (f : nat -> R) (L : R) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall n : nat, (N <= n)%nat -> Rabs (f n - L) < eps.

(******************************************************************************)
(* convergent_R 与 Un_cv 等价                                                  *)
(******************************************************************************)

Lemma convergent_R_eq_Un_cv :
  forall f L, convergent_R f L <-> Un_cv f L.
Proof.
  intros f L. split.
  - intros H eps Heps. destruct (H eps Heps) as [N HN].
    exists N. intros n Hn. unfold Rdist. apply HN. exact Hn.
  - intros H eps Heps. destruct (H eps Heps) as [N HN].
    exists N. intros n Hn. unfold Rdist in HN. apply HN. exact Hn.
Qed.

(******************************************************************************)
(* bounded_above 与 has_ub 等价                                                *)
(******************************************************************************)

Lemma bounded_above_eq_has_ub :
  forall f, bounded_above f <-> has_ub f.
Proof.
  intro f. split.
  - intros [M HM]. unfold has_ub, bound. exists M.
    intros x [i Hx]. rewrite Hx. apply HM.
  - intros H. unfold has_ub, bound in H.
    destruct H as [M HM]. exists M.
    intro n. apply (HM (f n)). exists n. reflexivity.
Qed.

(******************************************************************************)
(* bounded_below 与 has_lb 等价                                                *)
(******************************************************************************)

Lemma bounded_below_eq_has_lb :
  forall f, bounded_below f <-> has_lb f.
Proof.
  intro f. split.
  - intros [m Hm]. unfold has_lb, bound. exists (- m).
    intros x [i Hx]. rewrite Hx. unfold opp_seq.
    assert (H : m <= f i). { apply Hm. }
    lra.
  - intros H. unfold has_lb, bound in H. destruct H as [M HM].
    exists (- M). intro n.
    specialize (HM (- f n)).
    assert (H1 : EUn (opp_seq f) (- f n)).
    { unfold EUn, opp_seq. exists n. reflexivity. }
    specialize (HM H1). unfold opp_seq in HM. lra.
Qed.

(******************************************************************************)
(* 引理：递增序列 f n >= f 0                                                  *)
(******************************************************************************)

Lemma increasing_ge_f0 :
  forall f n, increasing f -> f 0%nat <= f n.
Proof.
  intros f n Hinc. induction n as [|n IH].
  - lra.
  - specialize (Hinc n). lra.
Qed.

(******************************************************************************)
(* 引理：递减序列 f n <= f 0                                                  *)
(******************************************************************************)

Lemma decreasing_le_f0 :
  forall f n, decreasing f -> f n <= f 0%nat.
Proof.
  intros f n Hdec. induction n as [|n IH].
  - lra.
  - specialize (Hdec n). lra.
Qed.

(******************************************************************************)
(* 引理：收敛 ⟹ 有界 (使用标准库 maj_by_pos)                                  *)
(******************************************************************************)

Lemma convergent_R_bounded :
  forall f L, convergent_R f L -> bounded_seq_R f.
Proof.
  intros f L Hconv.
  apply convergent_R_eq_Un_cv in Hconv.
  assert (Hcauchy : Cauchy_crit f).
  { apply CV_Cauchy. exists L. exact Hconv. }
  assert (Hub : has_ub f).
  { apply cauchy_maj. exact Hcauchy. }
  assert (Hlb : has_lb f).
  { apply cauchy_min. exact Hcauchy. }
  split.
  - apply bounded_above_eq_has_ub. exact Hub.
  - apply bounded_below_eq_has_lb. exact Hlb.
Qed.

(******************************************************************************)
(* 引理：递增有上界 ⟹ 收敛 (使用标准库 growing_cv)                            *)
(******************************************************************************)

Lemma increasing_bounded_above_convergent :
  forall f, increasing f -> bounded_above f ->
  exists L : R, convergent_R f L.
Proof.
  intros f Hinc Hba.
  apply bounded_above_eq_has_ub in Hba.
  destruct (growing_cv f Hinc Hba) as [L HL].
  exists L. apply convergent_R_eq_Un_cv. exact HL.
Qed.

(******************************************************************************)
(* 引理：递减有下界 ⟹ 收敛 (使用标准库 decreasing_cv)                         *)
(******************************************************************************)

Lemma decreasing_bounded_below_convergent :
  forall f, decreasing f -> bounded_below f ->
  exists L : R, convergent_R f L.
Proof.
  intros f Hdec Hbb.
  apply bounded_below_eq_has_lb in Hbb.
  destruct (decreasing_cv f Hdec Hbb) as [L HL].
  exists L. apply convergent_R_eq_Un_cv. exact HL.
Qed.

(******************************************************************************)
(* 主定理：单调序列收敛 ⟺ 有界                                                *)
(******************************************************************************)

Theorem monotone_convergent_iff_bounded :
  forall f, monotone f ->
  (exists L : R, convergent_R f L) <-> bounded_seq_R f.
Proof.
  intros f Hmono. split.
  - (* 收敛 ⟹ 有界 *)
    intros [L Hconv]. exact (convergent_R_bounded f L Hconv).
  - (* 有界 ⟹ 收敛 *)
    intros [Hba Hbb].
    destruct Hmono as [Hinc | Hdec].
    + apply increasing_bounded_above_convergent. exact Hinc. exact Hba.
    + apply decreasing_bounded_below_convergent. exact Hdec. exact Hbb.
Qed.
