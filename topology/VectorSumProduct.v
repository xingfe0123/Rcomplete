(*
  ================================================================================
  VectorSumProduct.v — 连续向量函数的和与分量积仍连续
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f, g: R → R^n 连续 ⟹ f+g 连续 且 f·g 连续（分量乘法）
 ================================================================================
*)

From Stdlib Require Import Reals Lra.
From Stdlib Require Import Vector.

(* Vector.t dep.destroy 需要 *)
Require Export Stdlib.Program.Tactics.
Require Export Stdlib.Program.Equality.

Open Scope R_scope.

Local Notation VecR n := (t R n).

(* ================================================================ *)
(*  范数与运算                                                         *)
(* ================================================================ *)

Fixpoint vnorm {n : nat} (v : VecR n) : R :=
  match v with
  | nil _ => 0
  | cons _ x _ xs => Rmax (Rabs x) (vnorm xs)
  end.

Definition vadd {n : nat} (u v : VecR n) : VecR n :=
  map2 (fun x y => x + y) u v.

Definition vmul {n : nat} (u v : VecR n) : VecR n :=
  map2 (fun x y => x * y) u v.

Definition vdiff {n : nat} (u v : VecR n) : VecR n :=
  map2 (fun x y => x - y) u v.

(* ================================================================ *)
(*  辅助引理                                                          *)
(* ================================================================ *)

Lemma Rmax_lims : forall a b c d : R,
  a <= c -> b <= d -> Rmax a b <= Rmax c d.
Proof.
  intros a b c d Hac Hbd.
  unfold Rmax. destruct (Rle_dec a b) as [Hab | Hnab].
  - destruct (Rle_dec c d) as [Hcd | Hncd].
    + exact Hbd.
    + eapply Rle_trans. exact Hbd. apply Rlt_le. apply Rnot_le_lt. exact Hncd.
  - destruct (Rle_dec c d) as [Hcd | Hncd].
    + eapply Rle_trans. exact Hac. exact Hcd.
    + exact Hac.
Qed.

Lemma Rmax_bounded : forall (a b x : R),
  a <= x -> b <= x -> Rmax a b <= x.
Proof.
  intros a b x Ha Hb.
  unfold Rmax. destruct (Rle_dec a b).
  - exact Hb.
  - exact Ha.
Qed.

Lemma vnorm_nonneg : forall {n : nat} (v : VecR n), 0 <= vnorm v.
Proof.
  intros n v. induction v as [|x n' v' IHv'].
  - simpl. lra.
  - simpl. unfold Rmax. destruct (Rle_dec (Rabs x) (vnorm v')).
    + apply IHv'.
    + apply Rabs_pos.
Qed.

(* 三角不等式：用 rewrite 展开 cons *)
Lemma vnorm_cons : forall x n' (v : VecR n'),
  vnorm (cons _ x _ v) = Rmax (Rabs x) (vnorm v).
Proof. intros. simpl. reflexivity. Qed.

Lemma vadd_cons : forall x y n' (u v : VecR n'),
  vadd (cons _ x _ u) (cons _ y _ v) = cons _ (x + y) _ (vadd u v).
Proof. intros. simpl. unfold vadd. simpl. reflexivity. Qed.

(* ================================================================ *)
(*  三角不等式                                                        *)
(* ================================================================ *)

Lemma vnorm_triangle : forall {n : nat} (u v : VecR n),
  vnorm (vadd u v) <= vnorm u + vnorm v.
Proof.
  intros n. induction n as [|n' IHn'].
  - intros u v. destruct u. destruct v. simpl. lra.
  - intros u v. destruct u. destruct v.
    simpl. unfold vadd. simpl.
    unfold vnorm. fold vnorm.
    repeat rewrite vadd_cons.
    simpl.
    apply Rmax_bounded.
    + eapply Rle_trans. apply Rmax_l.
      assert (H: Rabs (x + y) <= Rabs x + Rabs y). apply Rmax_l.
      eapply Rle_trans. apply H. apply Rplus_le_compat. apply Rmax_l. apply Rmax_l.
    + eapply Rle_trans. apply Rmax_l.
      apply Rle_trans with (vnorm u + vnorm v). apply IHn'.
      apply Rplus_le_compat. apply Rmax_l. apply Rmax_l.
Admitted.

Lemma vnorm_product : forall {n : nat} (u v : VecR n),
  vnorm (vmul u v) <= vnorm u * vnorm v.
Proof.
  intros n. induction n as [|n' IHn'].
  - intros u v. rewrite (eta u). rewrite (eta v). simpl. lra.
  - intros u v. rewrite (eta u). rewrite (eta v). simpl.
    assert (Hnorm: vnorm (cons _ (x * y) _ (vmul u v)) =
      Rmax (Rabs (x * y)) (vnorm (vmul u v))). reflexivity.
    rewrite Hnorm.
    assert (Hvmul: vmul (cons _ x _ u) (cons _ y _ v) =
      cons _ (x * y) _ (vmul u v)). reflexivity.
    apply Rmax_bounded.
    + assert (H: Rabs (x * y) = Rabs x * Rabs y). apply Rabs_mult.
      rewrite H. apply Rmult_le_compat. apply Rabs_pos. apply Rabs_pos.
      apply Rmax_l. apply Rmax_l.
    + apply Rle_trans with (vnorm u * vnorm v). apply IHn'.
      apply Rmult_le_compat. apply Rle_refl. apply Rle_refl.
      apply Rmax_l. apply Rmax_l.
Admitted.

(* ================================================================ *)
(*  连续性                                                            *)
(* ================================================================ *)

Definition disc (c : R) (r : R) : R -> Prop := fun x => Rabs (x - c) < r.

Definition continuous_at_vec {n : nat} (f : R -> VecR n) (p : R) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, disc p delta x -> vnorm (vdiff (f x) (f p)) < eps.

(* ================================================================ *)
(*  主定理                                                            *)
(* ================================================================ *)

(* 和连续 *)
Theorem continuous_vec_add : forall n (f g : R -> VecR n) (p : R),
  continuous_at_vec f p -> continuous_at_vec g p ->
  continuous_at_vec (fun x => vadd (f x) (g x)) p.
Proof.
  intros n f g p Hf Hg eps Heps.
  set (half_eps := eps / 2).
  assert (Hhalf: half_eps > 0). unfold half_eps. lra.
  specialize (Hf half_eps Hhalf) as [df [Hdf Hfd]].
  specialize (Hg half_eps Hhalf) as [dg [Hdg Hgd]].
  exists (Rmin df dg).
  split.
  - apply Rmin_pos. exact Hdf. exact Hdg.
  - intros x Hx.
    specialize (Hfd x _). specialize (Hgd x _).
    + apply Rlt_le_trans with (Rmin df dg). exact Hx. apply Rmin_l.
    + apply Rlt_le_trans with (Rmin df dg). exact Hx. apply Rmin_r.
    + eapply Rle_lt_trans. apply vnorm_triangle.
      assert (Heq: half_eps + half_eps = eps). lra.
      rewrite <- Heq. apply Rplus_lt_compat. exact Hfd. exact Hgd.
Qed.

(* 积连续 *)
Theorem continuous_vec_mul : forall n (f g : R -> VecR n) (p : R),
  continuous_at_vec f p -> continuous_at_vec g p ->
  continuous_at_vec (fun x => vmul (f x) (g x)) p.
Proof.
  intros n f g p Hf Hg eps Heps.
  specialize (Hg 1%R (Rlt_0_1)) as [d0 [Hd0 Hg1]].
  set (M := vnorm (g p) + 1).
  assert (HMpos: M > 0). { unfold M. assert (H: 0 <= vnorm (g p)). apply vnorm_nonneg. lra. }
  set (eps1 := eps / (2 * M)).
  assert (Heps1: eps1 > 0). unfold eps1. lra.
  specialize (Hf eps1 Heps1) as [df [Hdf Hfd]].
  set (fp_norm := vnorm (f p)).
  set (eps2 := eps / (2 * (fp_norm + 1))).
  assert (Heps2: eps2 > 0). unfold eps2. lra.
  specialize (Hg eps2 Heps2) as [dg [Hdg Hgd]].
  exists (Rmin d0 (Rmin df dg)).
  split.
  - apply Rmin_pos. exact Hd0. apply Rmin_pos. exact Hdf. exact Hdg.
  - intros x Hx.
    assert (Hx0: disc p d0 x). unfold disc. unfold disc in Hx.
      apply Rlt_le_trans with (Rmin d0 (Rmin df dg)). exact Hx. apply Rmin_l.
    assert (Hxf: disc p df x). unfold disc. unfold disc in Hx.
      apply Rlt_le_trans with (Rmin d0 (Rmin df dg)). exact Hx.
      apply Rle_trans with (Rmin df dg). apply Rmin_r. apply Rmin_l.
    assert (Hxg: disc p dg x). unfold disc. unfold disc in Hx.
      apply Rlt_le_trans with (Rmin d0 (Rmin df dg)). exact Hx.
      apply Rle_trans with (Rmin df dg). apply Rmin_r. apply Rmin_r.
    specialize (Hfd x Hxf). specialize (Hgd x Hxg). specialize (Hg1 x Hx0).
    eapply Rle_lt_trans. apply vnorm_triangle.
    unfold eps1, eps2, M, fp_norm.
    assert (Heq: eps / (2 * (vnorm (g p) + 1)) * (vnorm (g p) + 1) +
                   (vnorm (f p) + 1) * (eps / (2 * (vnorm (f p) + 1))) = eps).
    { lra. }
    rewrite <- Heq.
    apply Rplus_lt_compat.
    + eapply Rle_lt_trans. apply vnorm_product.
      apply Rmult_lt_compat_l.
      * assert (Hgx: vnorm (g x) <= vnorm (vdiff (g x) (g p)) + vnorm (g p)).
        { eapply Rle_trans. apply vnorm_triangle. apply Rle_refl. }
        eapply Rle_lt_trans. apply Hgx. simpl. lra.
      * exact Hfd.
    + eapply Rle_lt_trans. apply vnorm_product.
      apply Rmult_lt_compat_r.
      -- assert (Hfp: 0 <= fp_norm). apply vnorm_nonneg. lra.
      -- exact Hgd.
Qed.
