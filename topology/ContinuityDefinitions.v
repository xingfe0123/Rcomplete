(*
  ================================================================================
  ContinuityDefinitions.v — 连续性的原像定义与 ε-δ 定义的等价性
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  本文件形式化证明以下等价关系（函数 f: R → R 在点 x₀ 处连续）：

    (ε-δ 定义)    ∀ ε > 0, ∃ δ > 0, ∀ x, Rabs (x - x₀) < δ → Rabs (f x - f x₀) < ε
    ⟺
    (原像定义)    ∀ V, 开集 V → f(x₀) ∈ V → ∃ U, 开集 U → x₀ ∈ U → U ⊆ f⁻¹(V)

  核心思路：
  - (ε-δ ⟹ 原像): 取 V 开集含 f(x₀)，由开集定义得 ε-球 ⊆ V，用 ε-δ 得 δ-球，
    则 δ-球 ⊆ f⁻¹(V)
  - (原像 ⟹ ε-δ): 取 ε > 0，V = (f(x₀)-ε, f(x₀)+ε) 是开集含 f(x₀)，
    由原像定义得开集 U 含 x₀，U ⊆ f⁻¹(V)，再由开集定义得 δ-球 ⊆ U

  ================================================================================
*)

From Stdlib Require Import Reals Lra ClassicalEpsilon.

Open Scope R_scope.

(* ================================================================ *)
(*  1. R 中的开集（由开区间定义）                                    *)
(* ================================================================ *)

Definition open_R (U : R -> Prop) : Prop :=
  forall x, U x -> exists r, r > 0 /\
    forall y, Rabs (y - x) < r -> U y.

(* 开球定义 *)
Definition disc (c : R) (r : R) : R -> Prop :=
  fun x => Rabs (x - c) < r.

(* ================================================================ *)
(*  2. 原像定义与 ε-δ 定义                                           *)
(* ================================================================ *)

Definition continuous_eps_delta_at (f : R -> R) (x0 : R) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, disc x0 delta x -> disc (f x0) eps (f x).

Definition continuous_preimage_at (f : R -> R) (x0 : R) : Prop :=
  forall V, open_R V -> V (f x0) ->
    exists U : R -> Prop, open_R U /\ U x0 /\
      forall x, U x -> V (f x).

(* ================================================================ *)
(*  3. 辅助引理                                                       *)
(* ================================================================ *)

(* 开球是开集 *)
Lemma disc_is_open : forall c r, open_R (disc c r).
Proof.
  intros c r x Hx.
  exists (r - Rabs (x - c)).
  split.
  - unfold disc in Hx. lra.
  - intros y Hy.
    unfold disc.
    unfold disc in Hx.
    pose proof (Rabs_triang (y - x) (x - c)) as Htri.
    assert (Heq: (y - x) + (x - c) = y - c) by lra.
    rewrite Heq in Htri.
    lra.
Qed.

(* Rabs 三角不等式 *)
Lemma Rabs_triang : forall x y, Rabs (x + y) <= Rabs x + Rabs y.
Proof.
  intros x y.
  destruct (Rcase_abs x) as [Hx|Hx].
  - destruct (Rcase_abs y) as [Hy|Hy].
    + rewrite Rabs_left with (1 := Hx).
      rewrite Rabs_left with (1 := Hy).
      assert (Hxy: x + y < 0) by lra.
      rewrite Rabs_left with (1 := Hxy).
      lra.
    + rewrite Rabs_left with (1 := Hx).
      rewrite Rabs_right with (1 := Hy).
      destruct (Rcase_abs (x + y)) as [Hxy|Hxy].
      * rewrite Rabs_left with (1 := Hxy). lra.
      * rewrite Rabs_right with (1 := Hxy). lra.
  - destruct (Rcase_abs y) as [Hy|Hy].
    + rewrite Rabs_right with (1 := Hx).
      rewrite Rabs_left with (1 := Hy).
      destruct (Rcase_abs (x + y)) as [Hxy|Hxy].
      * rewrite Rabs_left with (1 := Hxy). lra.
      * rewrite Rabs_right with (1 := Hxy). lra.
    + rewrite Rabs_right with (1 := Hx).
      rewrite Rabs_right with (1 := Hy).
      rewrite Rabs_right.
      lra.
      assert (Hxy: x + y >= 0) by lra. exact Hxy.
Qed.

(* ================================================================ *)
(*  4. 主要定理                                                       *)
(* ================================================================ *)

(* 方向 1: ε-δ ⟹ 原像 *)
Theorem eps_delta_impl_preimage : forall f x0,
  continuous_eps_delta_at f x0 -> continuous_preimage_at f x0.
Proof.
  intros f x0 Heps V HV Hfx0.
  unfold continuous_eps_delta_at in Heps.
  unfold open_R in HV.
  destruct (HV (f x0) Hfx0) as [eps [Heps_pos HdiscV]].
  destruct (Heps eps Heps_pos) as [delta [Hdelta_pos Hf]].
  exists (disc x0 delta).
  split.
  - apply disc_is_open.
  - split.
    + unfold disc. replace (x0 - x0) with 0 by lra.
      rewrite Rabs_R0. exact Hdelta_pos.
    + intros x Hx. apply HdiscV. exact (Hf x Hx).
Qed.

(* 方向 2: 原像 ⟹ ε-δ *)
Theorem preimage_impl_eps_delta : forall f x0,
  continuous_preimage_at f x0 -> continuous_eps_delta_at f x0.
Proof.
  intros f x0 Hpre eps Heps.
  unfold continuous_preimage_at in Hpre.
  assert (HV: open_R (disc (f x0) eps)).
  { apply disc_is_open. }
  assert (Hfx0: disc (f x0) eps (f x0)).
  { unfold disc. replace (f x0 - f x0) with 0 by lra.
    rewrite Rabs_R0. exact Heps. }
  destruct (Hpre (disc (f x0) eps) HV Hfx0) as [U [HU [Hx0U Hsub]]].
  unfold open_R in HU.
  destruct (HU x0 Hx0U) as [delta [Hdelta_pos HdiscU]].
  exists delta.
  split.
  - exact Hdelta_pos.
  - intros x Hx.
    apply (Hsub x (HdiscU x Hx)).
Qed.

(* 等价定理（分别用两个方向的蕴含） *)
Theorem continuous_preimage_impl_eps_delta : forall f x0,
  continuous_preimage_at f x0 -> continuous_eps_delta_at f x0.
Proof.
  exact preimage_impl_eps_delta.
Qed.

Theorem continuous_eps_delta_impl_preimage : forall f x0,
  continuous_eps_delta_at f x0 -> continuous_preimage_at f x0.
Proof.
  exact eps_delta_impl_preimage.
Qed.
