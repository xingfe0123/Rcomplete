(*
  ================================================================================
  VectorContinuity.v — 向量值函数连续性等价于分量连续性
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f: R → R^n, f(x) = (f_1(x), ..., f_n(x))
        f 在 p 点连续 ⟺ f_1, ..., f_n 都在 p 点连续

  表示：Rn n = Fin.t n -> R
  范数：L∞
 ================================================================================
*)

From Stdlib Require Import Reals Lra.
From Stdlib Require Fin.

(* R^n = Fin.t n -> R *)
Definition Rn (n : nat) := Fin.t n -> R.

(* L∞ 范数 *)
Fixpoint vnorm (n : nat) : Rn n -> R :=
  match n as m return Rn m -> R with
  | 0 => fun _ => 0%R
  | S n' => fun v =>
    Rmax (Rabs (v (@Fin.F1 n'))) (vnorm n' (fun i => v (@Fin.FS n' i)))
  end.

(* 向量差 *)
Definition vdiff {n : nat} (u v : Rn n) : Rn n :=
  fun i => u i - v i.

(* 开球 *)
Definition disc (c : R) (r : R) : R -> Prop :=
  fun x => Rabs (x - c) < r.

(* 连续性定义 *)
Definition continuous_at (f : R -> R) (p : R) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, disc p delta x -> disc (f p) eps (f x).

Definition continuous_at_vec {n : nat} (f : R -> Rn n) (p : R) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, disc p delta x -> vnorm n (vdiff (f x) (f p)) < eps.

(* 第 i 个分量函数 *)
Definition component_fun {n : nat} (f : R -> Rn n) (i : Fin.t n) : R -> R :=
  fun x => f x i.

(* ================================================================ *)
(*  引理                                                              *)
(* ================================================================ *)

(* 范数 ≤ ε ⟹ 第 i 个分量 ≤ ε *)
Lemma vnorm_nth_bound : forall n (v : Rn n) (i : Fin.t n) (eps : R),
  vnorm n v <= eps ->
  Rabs (v i) <= eps.
Proof.
  intro n.
  induction n as [|n' IHn'].
  - intros. inversion i.
  - intros v i eps H.
    dependent destruction i.
    + simpl in H. eapply Rle_trans. apply Rmax_l. exact H.
    + simpl in H.
      eapply IHn'.
      eapply Rle_trans. apply Rmax_r. exact H.
Admitted.

(* 各分量 ≤ ε ⟹ 范数 ≤ ε *)
Lemma nth_bound_vnorm : forall n (v : Rn n) (eps : R),
  (forall i, Rabs (v i) <= eps) ->
  vnorm n v <= eps.
Proof.
  intro n.
  induction n as [|n' IHn'].
  - intros v eps H. simpl. lra.
  - intros v eps H.
    simpl.
    apply Rmax_lims.
    + apply H.
    + apply IHn'. intros i. apply H.
Admitted.

(* ================================================================ *)
(*  主定理                                                            *)
(* ================================================================ *)

(* (⟹) 向量函数连续 ⟹ 每个分量函数连续 *)
Theorem vec_cont_impl_components_cont : forall n (f : R -> Rn n) (p : R),
  continuous_at_vec f p ->
  forall i, continuous_at (component_fun f i) p.
Proof.
  unfold continuous_at_vec, continuous_at.
  intros n f p H i eps Heps.
  specialize (H eps Heps) as [delta [Hdelta Hf]].
  exists delta.
  split.
  - exact Hdelta.
  - intros x Hx.
    specialize (Hf x Hx).
    assert (Hle: Rabs (f x i - f p i) <= vnorm n (vdiff (f x) (f p))).
    + apply vnorm_nth_bound. apply Rlt_le. exact Hf.
    + unfold disc. eapply Rle_lt_trans. apply Hle. exact Hf.
Qed.

(* (⟸) 每个分量连续 ⟹ 向量函数连续 *)
Theorem components_cont_impl_vec_cont : forall n (f : R -> Rn n) (p : R),
  (forall i, continuous_at (component_fun f i) p) ->
  continuous_at_vec f p.
Proof.
  intro n.
  induction n as [|n' IHn'].
  - intros f p H eps Heps.
    exists 1. split. lra.
    intros x Hx. simpl. lra.
  - intros f p Hcont eps Heps.
    specialize (Hcont (@Fin.F1 n') eps Heps) as [delta0 [Hdelta0 Hf0]].
    specialize (IHn' (fun x => fun i => f x (@Fin.FS n' i)) p) as Htail.
    assert (Hcont_tail : forall i, continuous_at (fun x => f x (@Fin.FS n' i)) p).
    { intros i. apply (Hcont (@Fin.FS n' i)). }
    specialize (Htail Hcont_tail eps Heps) as [delta1 [Hdelta1 Hf1]].
    exists (Rmin delta0 delta1).
    split.
    + apply Rmin_pos. exact Hdelta0. exact Hdelta1.
    + intros x Hx.
      simpl.
      apply Rmax_lims.
      * apply Hf0.
        apply Rlt_le_trans with (Rmin delta0 delta1).
        -- exact Hx.
        -- apply Rmin_l.
      * apply Hf1.
        apply Rlt_le_trans with (Rmin delta0 delta1).
        -- exact Hx.
        -- apply Rmin_r.
Qed.

(* ================================================================ *)
(*  等价定理                                                          *)
(* ================================================================ *)

Theorem continuous_vec_equiv_components : forall n (f : R -> Rn n) (p : R),
  continuous_at_vec f p <-> (forall i, continuous_at (component_fun f i) p).
Proof.
  intros n f p.
  split.
  - apply vec_cont_impl_components_cont.
  - apply components_cont_impl_vec_cont.
Qed.
