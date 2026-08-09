(*
  ================================================================================
  LimitContinuity.v — 极限定义与连续性的等价性
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  本文件形式化证明：f 在 p 点连续 ⟺ lim_{x→p} f(x) = f(p)

  定义：
  - limit_at f p L := ∀ε>0, ∃δ>0, ∀x, disc p δ x ∧ x ≠ p → disc L ε (f x)
  - continuous_at f p  := ∀ε>0, ∃δ>0, ∀x, disc p δ x → disc (f p) ε (f x)

  ================================================================================
*)

From Stdlib Require Import Reals Lra.

Open Scope R_scope.

(* 开球 *)
Definition disc (c : R) (r : R) : R -> Prop :=
  fun x => Rabs (x - c) < r.

(* 连续性：ε-δ 定义 *)
Definition continuous_at (f : R -> R) (p : R) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, disc p delta x -> disc (f p) eps (f x).

(* 极限定义：lim_{x→p} f(x) = L
   ⟺ ∀ε>0, ∃δ>0, ∀x, 0 < |x-p| < δ → |f(x)-L| < ε *)
Definition limit_at (f : R -> R) (p L : R) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, disc p delta x /\ x <> p -> disc L eps (f x).

(* ================================================================ *)
(*  引理                                                              *)
(* ================================================================ *)

(* disc 自反性：p ∈ disc p r 当 r > 0 *)
Lemma disc_refl : forall p r, r > 0 -> disc p r p.
Proof.
  intros p r Hr.
  unfold disc.
  replace (p - p) with 0 by lra.
  rewrite Rabs_R0. exact Hr.
Qed.

(* ================================================================ *)
(*  主要定理                                                          *)
(* ================================================================ *)

(* 方向 1: 连续 ⟹ 极限存在且等于 f(p) *)
Theorem continuous_impl_limit : forall f p,
  continuous_at f p -> limit_at f p (f p).
Proof.
  intros f p Hcont.
  unfold continuous_at in Hcont.
  unfold limit_at.
  intros eps Heps.
  destruct (Hcont eps Heps) as [delta [Hdelta_pos Hf]].
  exists delta.
  split.
  - exact Hdelta_pos.
  - intros x [Hx _].
    apply Hf. exact Hx.
Qed.

(* 方向 2: lim_{x→p} f(x) = f(p) ⟹ 连续 *)
Theorem limit_impl_continuous : forall f p,
  limit_at f p (f p) -> continuous_at f p.
Proof.
  intros f p Hlim.
  unfold limit_at in Hlim.
  unfold continuous_at.
  intros eps Heps.
  destruct (Hlim eps Heps) as [delta [Hdelta_pos Hf]].
  exists delta.
  split.
  - exact Hdelta_pos.
  - intros x Hx.
    destruct (Req_dec x p) as [Heq|Hneq].
    + (* x = p: |f(x)-f(p)| = 0 < eps *)
      rewrite Heq.
      unfold disc.
      replace (f p - f p) with 0 by lra.
      rewrite Rabs_R0. exact Heps.
    + (* x ≠ p: 用极限定义 *)
      apply Hf.
      split.
      * exact Hx.
      * exact Hneq.
Qed.

(* 等价定理 *)
Theorem continuous_equiv_limit : forall f p,
  continuous_at f p <-> limit_at f p (f p).
Proof.
  intros f p.
  split.
  - exact (continuous_impl_limit f p).
  - exact (limit_impl_continuous f p).
Qed.
