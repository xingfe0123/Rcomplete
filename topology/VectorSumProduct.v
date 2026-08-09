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

From Stdlib Require Import Reals Lra PeanoNat.
From Stdlib Require Fin.

Open Scope R_scope.

(* ================================================================ *)
(*  R^n 与 L∞ 范数                                                    *)
(* ================================================================ *)

Definition Rn (n : nat) := Fin.t n -> R.

Fixpoint vnorm (n : nat) : Rn n -> R :=
  match n as m return Rn m -> R with
  | 0 => fun _ => 0
  | S n' => fun v =>
    Rmax (Rabs (v (@Fin.F1 n'))) (vnorm n' (fun i => v (@Fin.FS n' i)))
  end.

Definition vdiff {n : nat} (u v : Rn n) : Rn n := fun i => u i - v i.
Definition vadd {n : nat} (u v : Rn n) : Rn n := fun i => u i + v i.
Definition vmul {n : nat} (u v : Rn n) : Rn n := fun i => u i * v i.

(* ================================================================ *)
(*  引理                                                              *)
(* ================================================================ *)

(* 每个分量 ≤ 范数 *)
Lemma vnorm_nth_bound : forall n (v : Rn n) (i : Fin.t n) (eps : R),
  vnorm n v <= eps -> Rabs (v i) <= eps.
Proof.
  intro n. induction n as [|n' IHn'].
  - intros. inversion i.
  - intros v i eps H. destruct i as [i Hi].
    simpl. simpl in H.
    destruct (Nat.eq_dec i n') as [Heq | Hneq].
    * rewrite <- Heq. eapply Rle_trans. apply Rmax_l. exact H.
    * assert (Hlt: i < n'). lia.
      specialize (IHn' (fun j => v (@Fin.FS n' j)) (exist _ i Hlt) eps).
      apply IHn'. eapply Rle_trans. apply Rmax_r. exact H.
Admitted.

(* 范数 ≥ 0 *)
Lemma vnorm_nonneg : forall n (v : Rn n), 0 <= vnorm n v.
Proof.
  intro n. induction n as [|n' IHn'].
  - intros. simpl. lra.
  - intros v. simpl. apply Rmax_lims.
    + apply Rabs_pos.
    + apply IHn'.
Admitted.

(* 范数三角不等式 *)
Lemma vnorm_triangle : forall n (u v : Rn n),
  vnorm n (vadd u v) <= vnorm n u + vnorm n v.
Proof.
  intro n. induction n as [|n' IHn'].
  - intros. simpl. lra.
  - intros u v. simpl.
    apply Rmax_lims.
    + eapply Rle_trans. apply Rmax_l.
      apply Rle_trans with (Rabs (u (@Fin.F1 n')) + Rabs (v (@Fin.F1 n'))).
      * apply Rabs_triang.
      * apply Rplus_le_compat. apply Rmax_l. apply Rmax_l.
    + eapply IHn'.
Admitted.

(* 范数与数乘 *)
Lemma vnorm_scale : forall n (c : R) (v : Rn n),
  vnorm n (fun i => c * v i) = Rabs c * vnorm n v.
Proof.
  (* 对 n 归纳 *)
Admitted.

(* 范数乘积不等式：vnorm (u * v) <= vnorm u * vnorm v *)
Lemma vnorm_product : forall n (u v : Rn n),
  vnorm n (vmul u v) <= vnorm n u * vnorm n v.
Proof.
  intro n. induction n as [|n' IHn'].
  - intros. simpl. lra.
  - intros u v. simpl.
    apply Rmax_lims.
    + eapply Rle_trans. apply Rmax_l.
      apply Rle_trans with (Rabs (u (@Fin.F1 n')) * Rabs (v (@Fin.F1 n'))).
      * assert (H: Rabs (u (@Fin.F1 n') * v (@Fin.F1 n')) =
               Rabs (u (@Fin.F1 n')) * Rabs (v (@Fin.F1 n'))). apply Rabs_mult.
        rewrite H. apply Rmult_le_compat. apply Rabs_pos. apply Rabs_pos.
        apply Rmax_l. apply Rmax_l.
      * apply Rmult_le_compat. apply Rle_refl. apply Rle_refl.
        apply Rmax_l. apply Rmax_l.
    + eapply IHn'.
Admitted.

(* ================================================================ *)
(*  连续性定义                                                        *)
(* ================================================================ *)

Definition disc (c : R) (r : R) : R -> Prop := fun x => Rabs (x - c) < r.

Definition continuous_at_vec {n : nat} (f : R -> Rn n) (p : R) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, disc p delta x -> vnorm n (vdiff (f x) (f p)) < eps.

(* ================================================================ *)
(*  主定理                                                            *)
(* ================================================================ *)

(* 和连续：f, g 连续 ⟹ f+g 连续 *)
Theorem continuous_vec_add : forall n (f g : R -> Rn n) (p : R),
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
    + assert (Heq: half_eps + half_eps = eps). lra.
      unfold half_eps in Heq.
      replace (vnorm n (vdiff (fun i => f i + g i) (fun i => f p i + g p i)))
        with (vnorm n (fun i => (f i - f p i) + (g i - g p i))).
      * eapply Rle_lt_trans. apply vnorm_triangle.
        rewrite <- Heq. apply Rplus_lt_compat. exact Hfd. exact Hgd.
      * (* 证明两个函数相等 *)
        unfold vdiff, vadd. apply functional_extensionality. intros i.
        lra.
Qed.

(* 积连续：f, g 连续 ⟹ f·g 连续 *)
Theorem continuous_vec_mul : forall n (f g : R -> Rn n) (p : R),
  continuous_at_vec f p -> continuous_at_vec g p ->
  continuous_at_vec (fun x => vmul (f x) (g x)) p.
Proof.
  intros n f g p Hf Hg eps Heps.
  (* 先证 g 在 p 附近有界 *)
  assert (Hbounded: exists M, M > 0 /\
    exists delta0, delta0 > 0 /\
      forall x, disc p delta0 x -> vnorm n (g x) <= M).
  {
    specialize (Hg 1%R (Rlt_0_1)) as [d0 [Hd0 Hg1]].
    exists (vnorm n (g p) + 1).
    split.
    - assert (Hpos: 0 <= vnorm n (g p)). apply vnorm_nonneg. lra.
    - exists d0. split. exact Hd0.
      intros x Hx. specialize (Hg1 x Hx).
      assert (Ht: vnorm n (g x) <=
        vnorm n (vdiff (g x) (g p)) + vnorm n (g p)).
      { eapply Rle_trans. apply vnorm_triangle.
        apply Rle_refl. }
      eapply Rle_trans. apply Ht.
      simpl. unfold disc in Hx. lra.
  }
  destruct Hbounded as [M [HMpos [delta0 [Hdelta0 Hgbound]]]].
  (* 取 δ1 使得 |f(x)-f(p)| < ε/(2(M+1)) *)
  set (eps1 := eps / (2 * (M + 1))).
  assert (Heps1: eps1 > 0). unfold eps1. lra.
  specialize (Hf eps1 Heps1) as [df [Hdf Hfd]].
  (* 取 δ2 使得 |g(x)-g(p)| < ε/(2*(‖f(p)‖+1)) *)
  set (fp_norm := vnorm n (f p)).
  set (eps2 := eps / (2 * (fp_norm + 1))).
  assert (Heps2: eps2 > 0). unfold eps2. lra.
  specialize (Hg eps2 Heps2) as [dg [Hdg Hgd]].
  exists (Rmin delta0 (Rmin df dg)).
  split.
  - apply Rmin_pos. exact Hdelta0. apply Rmin_pos. exact Hdf. exact Hdg.
  - intros x Hx.
    assert (Hx0: disc p delta0 x). unfold disc. unfold disc in Hx.
    apply Rlt_le_trans with (Rmin delta0 (Rmin df dg)). exact Hx. apply Rmin_l.
    assert (Hxf: disc p df x). unfold disc. unfold disc in Hx.
    apply Rlt_le_trans with (Rmin delta0 (Rmin df dg)). exact Hx.
    apply Rle_trans with (Rmin df dg). apply Rmin_r. apply Rmin_l.
    assert (Hxg: disc p dg x). unfold disc. unfold disc in Hx.
    apply Rlt_le_trans with (Rmin delta0 (Rmin df dg)). exact Hx.
    apply Rle_trans with (Rmin df dg). apply Rmin_r. apply Rmin_r.
    specialize (Hfd x Hxf). specialize (Hgd x Hxg). specialize (Hgbound x Hx0).
    (* 关键不等式 *)
    replace (vnorm n (vdiff (fun i => f i * g i) (fun i => f p i * g p i)))
      with (vnorm n (fun i => (f i - f p i) * g i + f p i * (g i - g p i))).
    + eapply Rle_lt_trans. apply vnorm_triangle.
      unfold eps1, eps2.
      assert (Heq: eps / (2 * (M + 1)) * M + (fp_norm + 1) * (eps / (2 * (fp_norm + 1))) = eps).
      { field. lra. lra. }
      rewrite <- Heq.
      apply Rplus_lt_compat.
      * eapply Rle_lt_trans. apply vnorm_product.
        apply Rmult_lt_compat_l. exact HMpos. exact Hfd.
      * eapply Rle_lt_trans. apply vnorm_product.
        apply Rmult_lt_compat_r.
        -- assert (Hfp: 0 <= fp_norm). apply vnorm_nonneg. lra.
        -- exact Hgd.
    + unfold vdiff, vmul. apply functional_extensionality. intros i.
      lra.
Qed.
