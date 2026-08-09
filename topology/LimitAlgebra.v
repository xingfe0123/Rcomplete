(*
  ================================================================================
  LimitAlgebra.v — 极限的四则运算
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f, g 在 E 上定义，lim_{t->x} f(t) = A, lim_{t->x} g(t) = B
    1) 极限唯一：lim f(t) = A' → A' = A
    2) 和：lim (f+g)(t) = A + B
    3) 积：lim (fg)(t) = AB
    4) 商：lim (f/g)(t) = A/B （B ≠ 0）
  ================================================================================
*)

From Stdlib Require Import Reals Lra ClassicalEpsilon.

Open Scope R_scope.

(* ================================================================ *)
(*  定义                                                              *)
(* ================================================================ *)

(* E ⊆ R 的子集，x 是 E 的极限点 *)
Definition limit_point (E : R -> Prop) (x : R) : Prop :=
  forall delta, delta > 0 -> exists y, E y /\ y <> x /\ Rabs (y - x) < delta.

(* lim_{t->x} f(t) = A *)
Definition limit (E : R -> Prop) (f : R -> R) (x A : R) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall t, E t -> t <> x -> Rabs (t - x) < delta -> Rabs (f t - A) < eps.

(* ================================================================ *)
(*  引理                                                              *)
(* ================================================================ *)

(* 极限唯一性 *)
Lemma limit_unique :
  forall (E : R -> Prop) (f : R -> R) (x A A' : R),
  limit_point E x ->
  limit E f x A ->
  limit E f x A' ->
  A = A'.
Proof.
  intros E f x A A' Hpt HlimA HlimA'.
  (* 反证：假设 A ≠ A' *)
  destruct (Rtotal_order A A') as [Hlt|[Heq|Hgt]].
  - (* A < A' *)
    assert (Heps: (A' - A) / 2 > 0). lra.
    specialize (HlimA ((A' - A) / 2) Heps) as [delta1 [Hdelta1 Hf1]].
    specialize (HlimA' ((A' - A) / 2) Heps) as [delta2 [Hdelta2 Hf2]].
    set (delta := Rmin delta1 delta2).
    assert (Hdelta: delta > 0). { apply Rmin_case. exact Hdelta1. exact Hdelta2. }
    specialize (Hpt delta Hdelta) as [y [Hy [Hyx Hy_delta]]].
    assert (Hf1_y: Rabs (f y - A) < (A' - A) / 2).
    { apply Hf1. exact Hy. exact Hyx. apply Rlt_le_trans with delta. exact Hy_delta. apply Rmin_l. }
    assert (Hf2_y: Rabs (f y - A') < (A' - A) / 2).
    { apply Hf2. exact Hy. exact Hyx. apply Rlt_le_trans with delta. exact Hy_delta. apply Rmin_r. }
    (* 矛盾：A' - A < A' - A *)
    assert (Hcontr: A' - A < A' - A).
    { apply Rabs_def2 in Hf1_y.
      apply Rabs_def2 in Hf2_y.
      lra.
    }
    lra.
  - exact Heq.
  - (* A > A' ：对称 *)
    assert (Heps: (A - A') / 2 > 0). lra.
    specialize (HlimA ((A - A') / 2) Heps) as [delta1 [Hdelta1 Hf1]].
    specialize (HlimA' ((A - A') / 2) Heps) as [delta2 [Hdelta2 Hf2]].
    set (delta := Rmin delta1 delta2).
    assert (Hdelta: delta > 0). { apply Rmin_case. exact Hdelta1. exact Hdelta2. }
    specialize (Hpt delta Hdelta) as [y [Hy [Hyx Hy_delta]]].
    assert (Hf1_y: Rabs (f y - A) < (A - A') / 2).
    { apply Hf1. exact Hy. exact Hyx. apply Rlt_le_trans with delta. exact Hy_delta. apply Rmin_l. }
    assert (Hf2_y: Rabs (f y - A') < (A - A') / 2).
    { apply Hf2. exact Hy. exact Hyx. apply Rlt_le_trans with delta. exact Hy_delta. apply Rmin_r. }
    assert (Hcontr: A - A' < A - A').
    { apply Rabs_def2 in Hf1_y.
      apply Rabs_def2 in Hf2_y.
      lra.
    }
    lra.
Qed.
(* 局部有界性：极限存在 → 局部有界 *)
Lemma limit_bounded :
  forall (E : R -> Prop) (f : R -> R) (x A : R),
  limit E f x A ->
  exists delta, delta > 0 /\
    exists M, forall t, E t -> t <> x -> Rabs (t - x) < delta -> Rabs (f t) <= M.
Proof.
  intros E f x A Hlim.
  specialize (Hlim 1) as [delta [Hdelta Hf]].
  - lra.
  - exists delta. split. exact Hdelta.
    exists (Rabs A + 1). intros t Ht Htx Ht_delta.
    specialize (Hf t Ht Htx Ht_delta).
    assert (Heq: f t = (f t - A) + A). lra.
    rewrite Heq.
    assert (Rabs ((f t - A) + A) <= Rabs (f t - A) + Rabs A). { apply Rabs_triang. }
    lra.
Qed.

(* ================================================================ *)
(*  四则运算                                                          *)
(* ================================================================ *)

(* 和的极限 *)
Theorem limit_plus :
  forall (E : R -> Prop) (f g : R -> R) (x A B : R),
  limit_point E x ->
  limit E f x A ->
  limit E g x B ->
  limit E (fun t => f t + g t) x (A + B).
Proof.
  intros E f g x A B Hpt HlimA HlimB.
  intros eps Heps.
  assert (Heps2: eps / 2 > 0). lra.
  specialize (HlimA (eps / 2) Heps2) as [delta1 [Hdelta1 Hf]].
  specialize (HlimB (eps / 2) Heps2) as [delta2 [Hdelta2 Hg]].
  exists (Rmin delta1 delta2). split.
  - apply Rmin_case. exact Hdelta1. exact Hdelta2.
  - intros t Ht Htx Ht_delta.
    specialize (Hf t Ht Htx (Rlt_le_trans _ _ _ Ht_delta (Rmin_l delta1 delta2))).
    specialize (Hg t Ht Htx (Rlt_le_trans _ _ _ Ht_delta (Rmin_r delta1 delta2))).
    assert (Heq: (f t + g t) - (A + B) = (f t - A) + (g t - B)). ring.
    rewrite Heq.
    assert (Rabs ((f t - A) + (g t - B)) <= Rabs (f t - A) + Rabs (g t - B)). { apply Rabs_triang. }
    lra.
Qed.

(* 积的极限 *)
Theorem limit_mul :
  forall (E : R -> Prop) (f g : R -> R) (x A B : R),
  limit_point E x ->
  limit E f x A ->
  limit E g x B ->
  limit E (fun t => f t * g t) x (A * B).
Proof.
  intros E f g x A B Hpt HlimA HlimB.
  (* 利用恒等式：fg - AB = f(g - B) + B(f - A) *)
  assert (Hbound: exists delta0, delta0 > 0 /\
    exists M, forall t, E t -> t <> x -> Rabs (t - x) < delta0 -> Rabs (f t) <= M).
  { apply (@limit_bounded E f x A HlimA). }
  destruct Hbound as [delta0 [Hdelta0 [M Hf_bound]]].
  intros eps Heps.
  assert (Hpos_B: Rabs B + 1 > 0). { admit. }
  assert (Hpos_M: Rabs M + 1 > 0). { admit. }
  assert (Heps1: eps / (2 * (Rabs B + 1)) > 0). { apply Rdiv_lt_0_compat. lra. lra. }
  assert (Heps2: eps / (2 * (Rabs M + 1)) > 0). { apply Rdiv_lt_0_compat. lra. lra. }
  specialize (HlimA (eps / (2 * (Rabs B + 1))) Heps1) as [delta1 [Hdelta1 Hf]].
  specialize (HlimB (eps / (2 * (Rabs M + 1))) Heps2) as [delta2 [Hdelta2 Hg]].
  exists (Rmin delta0 (Rmin delta1 delta2)). split.
  - apply Rmin_case. exact Hdelta0. apply Rmin_case. exact Hdelta1. exact Hdelta2.
  - intros t Ht Htx Ht_delta.
    assert (Hf1: Rabs (t - x) < delta1).
    { apply Rlt_le_trans with (Rmin delta1 delta2). apply Rlt_le_trans with (Rmin delta0 (Rmin delta1 delta2)). exact Ht_delta. apply Rmin_r. apply Rmin_l. }
    assert (Hf2: Rabs (t - x) < delta2).
    { apply Rlt_le_trans with (Rmin delta1 delta2). apply Rlt_le_trans with (Rmin delta0 (Rmin delta1 delta2)). exact Ht_delta. apply Rmin_r. apply Rmin_r. }
    assert (Hf0: Rabs (t - x) < delta0).
    { apply Rlt_le_trans with (Rmin delta0 (Rmin delta1 delta2)). exact Ht_delta. apply Rmin_l. }
    specialize (Hf t Ht Htx Hf1).
    specialize (Hg t Ht Htx Hf2).
    specialize (Hf_bound t Ht Htx Hf0).
    assert (Heq: f t * g t - A * B = f t * (g t - B) + B * (f t - A)). ring.
    rewrite Heq.
    assert (Rabs (f t * (g t - B) + B * (f t - A)) <= Rabs (f t * (g t - B)) + Rabs (B * (f t - A))). { apply Rabs_triang. }
    assert (Rabs (f t * (g t - B)) + Rabs (B * (f t - A)) <= Rabs (f t) * Rabs (g t - B) + Rabs B * Rabs (f t - A)).
    { rewrite Rabs_mult. rewrite Rabs_mult. lra. }
    assert (Rabs (f t) * Rabs (g t - B) < eps / 2). { admit. }
    assert (Rabs B * Rabs (f t - A) < eps / 2). { admit. }
    lra.
Admitted.

(* 商的极限 *)
Theorem limit_quot :
  forall (E : R -> Prop) (f g : R -> R) (x A B : R),
  limit_point E x ->
  limit E f x A ->
  limit E g x B ->
  B <> 0 ->
  limit E (fun t => f t / g t) x (A / B).
Proof.
  intros E f g x A B Hpt HlimA HlimB Hneq.
  (* 先证 1/g → 1/B *)
  assert (Hbound: exists delta0, delta0 > 0 /\
    forall t, E t -> t <> x -> Rabs (t - x) < delta0 -> Rabs (g t) >= Rabs B / 2).
  { admit. }
  destruct Hbound as [delta0 [Hdelta0 Hg_bound]].
  intros eps Heps.
  assert (Heps1: eps * Rabs B^2 / 2 > 0). { admit. }
  assert (Heps2: eps * Rabs B / 4 > 0). { admit. }
  specialize (HlimA (eps * Rabs B^2 / 2) Heps1) as [delta1 [Hdelta1 Hf]].
  specialize (HlimB (eps * Rabs B / 4) Heps2) as [delta2 [Hdelta2 Hg]].
  exists (Rmin delta0 (Rmin delta1 delta2)). split.
  - apply Rmin_case. exact Hdelta0. apply Rmin_case. exact Hdelta1. exact Hdelta2.
  - intros t Ht Htx Ht_delta.
    specialize (Hf t Ht Htx (Rlt_trans _ _ _ Ht_delta (Rmin_r delta1 delta2 (Rmin_l delta0 (Rmin delta1 delta2))))).
    specialize (Hg t Ht Htx (Rlt_trans _ _ _ Ht_delta (Rmin_r delta1 delta2 (Rmin_r delta0 (Rmin delta1 delta2))))).
    specialize (Hg_bound t Ht Htx (Rlt_trans _ _ _ Ht_delta (Rmin_l delta0 (Rmin delta1 delta2)))).
    assert (Rabs (f t / g t - A / B) = Rabs ((f t * B - A * g t) / (g t * B))). lra.
    rewrite H.
    assert (Rabs ((f t * B - A * g t) / (g t * B)) <= (Rabs (f t - A) * Rabs B + Rabs A * Rabs (g t - B)) / (Rabs (g t) * Rabs B)). { lra. }
    assert ((Rabs (f t - A) * Rabs B + Rabs A * Rabs (g t - B)) / (Rabs (g t) * Rabs B) < eps). { lra. }
    lra.
Admitted.

Close Scope R_scope.
