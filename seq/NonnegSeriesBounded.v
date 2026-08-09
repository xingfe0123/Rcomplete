From Stdlib Require Import Reals RIneq Ranalysis.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import Rfunctions.
From Stdlib Require Import Rseries.
From Stdlib Require Import SeqProp.
From Stdlib Require Import Compare_dec.

Open Scope R_scope.

(******************************************************************************)
(* 部分和定义：S_n = a_0 + a_1 + ... + a_n                                    *)
(******************************************************************************)

Fixpoint partial_sum (a : nat -> R) (n : nat) : R :=
  match n with
  | 0%nat => a 0%nat
  | S k => partial_sum a k + a (S k)
  end.

(******************************************************************************)
(* 级数收敛定义                                                                *)
(******************************************************************************)

Definition series_convergent (a : nat -> R) (L : R) : Prop :=
  Un_cv (fun n => partial_sum a n) L.

Definition series_cv (a : nat -> R) : Prop :=
  exists L : R, series_convergent a L.

(******************************************************************************)
(* 部分和有界定义                                                               *)
(******************************************************************************)

Definition partial_sum_bounded (a : nat -> R) : Prop :=
  exists M : R, M > 0 /\ forall n : nat, Rabs (partial_sum a n) <= M.

(******************************************************************************)
(* 引理：partial_sum 递推                                                      *)
(******************************************************************************)

Lemma partial_sum_S :
  forall (a : nat -> R) (n : nat),
    partial_sum a (S n) = partial_sum a n + a (S n).
Proof. intros. reflexivity. Qed.

(******************************************************************************)
(* 引理：非负项级数的部分和递增                                                 *)
(******************************************************************************)

Lemma partial_sum_increasing :
  forall (a : nat -> R),
    (forall n : nat, a n >= 0) ->
    forall n m : nat, (n <= m)%nat ->
    partial_sum a n <= partial_sum a m.
Proof.
  intros a Hnneg n m Hnm.
  revert n Hnm.
  induction m as [|m IH].
  - intros n Hnm. simpl in Hnm. subst. lra.
  - intros n Hnm.
    destruct (Nat.eq_dec n (S m)) as [Heq | Hneq].
    + subst. lra.
    + assert (Hlt : (n <= m)%nat) by lia.
      specialize (IH n Hlt).
      rewrite partial_sum_S.
      assert (H : a (S m) >= 0) by apply Hnneg.
      lra.
Qed.

(******************************************************************************)
(* 引理：非负项级数部分和非负                                                   *)
(******************************************************************************)

Lemma partial_sum_nonneg :
  forall (a : nat -> R),
    (forall n : nat, a n >= 0) ->
    forall n : nat, partial_sum a n >= 0.
Proof.
  intros a Hnneg n.
  apply Rle_ge.
  induction n as [|n IH].
  - simpl. apply Rle_ge. apply Hnneg.
  - rewrite partial_sum_S.
    assert (H : a (S n) >= 0) by apply Hnneg.
    lra.
Qed.

(******************************************************************************)
(* 引理：非负项级数部分和的绝对值 = 自身                                        *)
(******************************************************************************)

Lemma partial_sum_abs_eq :
  forall (a : nat -> R),
    (forall n : nat, a n >= 0) ->
    forall n : nat, Rabs (partial_sum a n) = partial_sum a n.
Proof.
  intros a Hnneg n.
  apply Rabs_right.
  apply partial_sum_nonneg; exact Hnneg.
Qed.

(******************************************************************************)
(* 有限最大值定义：max_{i <= N} |S_i|                                          *)
(******************************************************************************)

Fixpoint max_partial_sum_abs (a : nat -> R) (N : nat) : R :=
  match N with
  | 0%nat => Rabs (partial_sum a 0%nat)
  | S k => Rmax (Rabs (partial_sum a (S k))) (max_partial_sum_abs a k)
  end.

(******************************************************************************)
(* 引理：max_partial_sum_abs 是上界                                             *)
(******************************************************************************)

Lemma max_partial_sum_abs_ub :
  forall (a : nat -> R) (N n : nat),
    (n <= N)%nat ->
    Rabs (partial_sum a n) <= max_partial_sum_abs a N.
Proof.
  intros a N n Hle.
  revert n Hle.
  induction N as [|N IH].
  - intros n Hle. simpl. subst. lra.
  - intros n Hle.
    destruct (Nat.eq_dec n (S N)) as [Heq | Hneq].
    + subst. simpl.
      unfold Rmax. destruct (Rle_dec (Rabs (partial_sum a (S N)))
                                 (max_partial_sum_abs a N)) as [Hd | Hd].
      * lra.
      * lra.
    + assert (Hlt : (n <= N)%nat) by lia.
      specialize (IH n Hlt).
      simpl.
      unfold Rmax. destruct (Rle_dec (Rabs (partial_sum a (S N)))
                                 (max_partial_sum_abs a N)) as [Hd | Hd].
      * apply Rle_trans with (max_partial_sum_abs a N); [exact IH | lra].
      * lra.
Qed.

(******************************************************************************)
(* 引理：max_partial_sum_abs >= 0                                              *)
(******************************************************************************)

Lemma max_partial_sum_abs_nonneg :
  forall (a : nat -> R) (N : nat), max_partial_sum_abs a N >= 0.
Proof.
  intros a N. induction N as [|N IH].
  - simpl. apply Rabs_pos.
  - simpl. unfold Rmax.
    destruct (Rle_dec (Rabs (partial_sum a (S N))) (max_partial_sum_abs a N)).
    + apply Rle_ge. lra.
    + apply Rle_ge. lra.
Qed.

(******************************************************************************)
(* 引理：收敛级数的部分和有界（通用版）                                         *)
(******************************************************************************)

Lemma convergent_bounded_general :
  forall (a : nat -> R),
    series_cv a ->
    exists M : R, forall n : nat, Rabs (partial_sum a n) <= M.
Proof.
  intros a [L Hconv].
  destruct (Hconv 1) as [N HN].
  - lra.
  - exists (Rabs L + 1 + max_partial_sum_abs a N).
    intro n.
    destruct (le_lt_dec N n) as [Hge | Hlt].
    + (* n >= N: |S_n - L| < 1, so |S_n| <= |L| + 1 *)
      specialize (HN n Hge). unfold Rdist in HN.
      assert (Habs : Rabs (partial_sum a n) <= Rabs L + 1).
      { apply Rle_trans with (Rabs (partial_sum a n - L) + Rabs L).
        - rewrite Rabs_triang. lra.
        - lra. }
      lra.
    + (* n < N: |S_n| <= max_{i<=N} |S_i| *)
      apply Rle_trans with (max_partial_sum_abs a N).
      * apply max_partial_sum_abs_ub. lia.
      * lra.
Qed.

(******************************************************************************)
(* 主定理：非负实数级数收敛 ⟺ 部分和有界                                       *)
(******************************************************************************)

Theorem nonneg_series_cv_iff_bounded :
  forall (a : nat -> R),
    (forall n : nat, a n >= 0) ->
    series_cv a <-> partial_sum_bounded a.
Proof.
  intros a Hnneg. split.
  - (* 收敛 ⟹ 有界 *)
    intros Hcv.
    destruct (convergent_bounded_general a Hcv) as [M HM].
    exists (M + 1). split. lra.
    intro n. apply Rle_trans with (Rabs (partial_sum a n)).
    + rewrite partial_sum_abs_eq by exact Hnneg. lra.
    + exact (HM n).
  - (* 有界 ⟹ 收敛：递增 + 有上界 ⟹ 收敛 *)
    intros [M [HMgt HMbnd]].
    assert (Hinc : Un_growing (fun n => partial_sum a n)).
    { red. intros n. rewrite partial_sum_S.
      assert (H : a (S n) >= 0) by apply Hnneg.
      lra. }
    assert (Hub : has_ub (fun n => partial_sum a n)).
    { unfold has_ub, bound, is_upper_bound.
      exists M. intros x [i Hx]. rewrite Hx.
      apply Rle_trans with (Rabs (partial_sum a i)).
      - rewrite partial_sum_abs_eq by exact Hnneg. lra.
      - exact (HMbnd i). }
    destruct (growing_cv (fun n => partial_sum a n) Hinc Hub) as [L HL].
    exists L. exact HL.
Qed.
