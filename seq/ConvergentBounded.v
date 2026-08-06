From Stdlib Require Import Reals RIneq Ranalysis.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Compare_dec.
From Stdlib Require Import Lists.List.

Open Scope R_scope.
Open Scope list_scope.

Import ListNotations.

(******************************************************************************)
(* 度量空间定义                                                                *)
(******************************************************************************)

Record MetricSpace : Type := {
  Carrier :> Type;
  dist : Carrier -> Carrier -> R;
  dist_self : forall x, dist x x = 0;
  dist_sym : forall x y, dist x y = dist y x;
  dist_triangle : forall x y z, dist x z <= dist x y + dist y z;
  dist_eq_ident : forall x y, dist x y = 0 -> x = y
}.

(******************************************************************************)
(* 距离非负性                                                                  *)
(******************************************************************************)

Lemma Rmult_le_compat_r_pos : forall r r1 r2 : R, r > 0 -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros r r1 r2 Hpos Hle.
  apply Rmult_le_compat_l.
  lra.
  exact Hle.
Qed.

Lemma dist_nonneg :
  forall (ms : MetricSpace) (x y : ms),
    0 <= @dist ms x y.

Proof.
  intros ms x y.
  assert (H1 : @dist ms x x <= @dist ms x y + @dist ms y x).
  { apply (@dist_triangle ms). }
  rewrite (@dist_self ms) in H1.
  assert (H2 : @dist ms x y + @dist ms y x = @dist ms x y + @dist ms x y).
  { f_equal. apply (@dist_sym ms). }
  rewrite H2 in H1.
  assert (H3 : @dist ms x y + @dist ms x y = 2 * @dist ms x y).
  { lra. }
  rewrite H3 in H1.
  assert (H4 : / 2 > 0).
  { apply Rinv_0_lt_compat. lra. }
  assert (H5 := Rmult_le_compat_r_pos (/ 2) 0 (2 * @dist ms x y) H4 H1).
  assert (H6a : / 2 * 2 = 1).
  { rewrite Rmult_comm. apply Rinv_r. lra. }
  assert (H6 : / 2 * (2 * @dist ms x y) = @dist ms x y).
  { rewrite <- Rmult_assoc. rewrite H6a. rewrite Rmult_1_l. lra. }
  assert (H7 : / 2 * 0 = 0).
  { apply Rmult_0_r. }
  rewrite H6 in H5. rewrite H7 in H5.
  exact H5.
Qed.

(******************************************************************************)
(* 序列收敛定义                                                                *)
(******************************************************************************)

Definition convergent (ms : MetricSpace) (p : nat -> ms) (p0 : ms) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall n : nat, (N <= n)%nat -> @dist ms (p n) p0 < eps.

(******************************************************************************)
(* 有界序列定义                                                                *)
(******************************************************************************)

Definition bounded_seq (ms : MetricSpace) (p : nat -> ms) : Prop :=
  exists (q : ms) (M : R), M > 0 /\ forall n : nat, @dist ms (p n) q < M.

(******************************************************************************)
(* 引理：1 > 0                                                                *)
(******************************************************************************)

Lemma one_pos : 1 > 0.
Proof. lra. Qed.

(******************************************************************************)
(* 引理：seq 0 n 包含所有小于 n 的自然数                                      *)
(******************************************************************************)

Lemma seq_lt_n (n i : nat) :
  (i < n)%nat -> In i (seq 0 n).
Proof.
  intros H. apply in_seq. lia.
Qed.

(******************************************************************************)
(* 引理：sum_list_nonneg                                                     *)
(******************************************************************************)

Lemma sum_list_nonneg (l : list R) :
  (forall x, In x l -> x >= 0) -> fold_right Rplus 0 l >= 0.
Proof.
  induction l as [|h t IH].
  - simpl. lra.
  - simpl. intros H.
    assert (Hh : h >= 0).
    { apply H. left. reflexivity. }
    assert (Ht : fold_right Rplus 0 t >= 0).
    { apply IH. intros x Hx. apply H. right. exact Hx. }
    lra.
Qed.

(******************************************************************************)
(* 引理：In Rplus 的性质                                                     *)
(******************************************************************************)

Lemma in_sum_ub (l : list R) (x : R) :
  In x l -> (forall y, In y l -> y >= 0) -> x <= fold_right Rplus 0 l.
Proof.
  induction l as [|h t IH].
  - simpl. tauto.
  - simpl. intros Hx Hnn.
    assert (Hh : h >= 0).
    { apply Hnn. left. reflexivity. }
    assert (Ht : fold_right Rplus 0 t >= 0).
    { apply sum_list_nonneg. intros y Hy. apply Hnn. right. exact Hy. }
    destruct Hx as [Hx | Hx].
    + subst. lra.
    + assert (Hx' : x <= fold_right Rplus 0 t).
      { apply IH. exact Hx. intros y Hy. apply Hnn. right. exact Hy. }
      lra.
Qed.

(******************************************************************************)
(* 定理：收敛序列有界                                                          *)
(******************************************************************************)

Theorem convergent_bounded :
  forall (ms : MetricSpace) (p : nat -> ms),
    (exists p0 : ms, convergent ms p p0) -> bounded_seq ms p.

Proof.
  intros ms p [p0 Hconv].
  specialize (Hconv 1 one_pos) as [N HN].
  set (l := map (fun i => @dist ms (p i) p0) (seq 0 N)).
  exists p0. exists (1 + fold_right Rplus 0 l).
  split.
  - (* M > 0 *)
    assert (Hsum : fold_right Rplus 0 l >= 0).
    { apply sum_list_nonneg. intros x Hx.
      apply in_map_iff in Hx as [i [Hi Hi']].
      rewrite <- Hi. apply Rle_ge. apply (dist_nonneg ms (p i) p0). }
    lra.
  - (* forall n, dist(p_n, p0) < M *)
    intro n.
    assert (Hsum : fold_right Rplus 0 l >= 0).
    { apply sum_list_nonneg. intros x Hx.
      apply in_map_iff in Hx as [i [Hi Hi']].
      rewrite <- Hi. apply Rle_ge. apply (dist_nonneg ms (p i) p0). }
    destruct (le_lt_dec N n) as [Hge | Hlt].
    + (* n >= N: 用收敛性 control *)
      specialize (HN n Hge).
      lra.
    + (* n < N: 用有限和 control *)
      assert (Hin : In (@dist ms (p n) p0) l).
      { unfold l. apply in_map_iff. exists n. split.
        - lra.
        - apply seq_lt_n. lia. }
      assert (Hmax : @dist ms (p n) p0 <= fold_right Rplus 0 l).
      { apply in_sum_ub. exact Hin.
        intros x Hx. apply in_map_iff in Hx as [i [Hi Hi']].
        rewrite <- Hi. apply Rle_ge. apply (dist_nonneg ms (p i) p0). }
      lra.
Qed.
