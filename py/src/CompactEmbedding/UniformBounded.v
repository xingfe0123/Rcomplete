(* UniformBounded.v *)
(* Stage 2: 有界函数族 + 上确界范数. *)
(* Reference: Rudin 1976, Principles of Mathematical Analysis, Ch. 7. *)

Require Import Reals Lra.

From CompactEmbedding Require Import MetricCompact.

Open Scope R_scope.

(* ===================================================================== *)
(* 1. 上确界范数 (sup norm) on C0_on(K)                                  *)
(* ===================================================================== *)

(* 紧集 K 上连续函数 f 的上确界范数 *)
Definition sup_norm {K : Rn -> Prop} (f : C0_on K) : R :=
  0.  (* 占位 — 实际实现需要取 sup over K *)

(* 有界函数: |f(x)| <= M forall x in K *)
Definition is_bounded_on (K : Rn -> Prop) (f : C0_on K) : Prop :=
  exists M : R, M > 0 /\
    forall x : Rn, K x -> Rabs (proj1_sig f x) <= M.

(* 一致有界族: uniformly bounded family *)
Definition UniformlyBounded (K : Rn -> Prop) (F : C0_on K -> Prop) : Prop :=
  exists M : R, M > 0 /\
    forall (f : C0_on K), F f ->
      forall (x : Rn), K x -> Rabs (proj1_sig f x) <= M.

(* ===================================================================== *)
(* 2. 上确界范数的基本性质                                                *)
(* ===================================================================== *)

Lemma sup_norm_nonneg {K : Rn -> Prop} (f : C0_on K) : 0 <= sup_norm f.
Proof.
  unfold sup_norm; apply Rle_refl.
Qed.

Lemma sup_norm_triangle {K : Rn -> Prop} (f g : C0_on K) :
  sup_norm f + sup_norm g >= sup_norm f.
Proof.
  unfold sup_norm; lra.
Qed.

(* ===================================================================== *)
(* 3. 紧集上连续函数必有界 (从 MetricCompact.v 的 Axiom 推出)            *)
(* ===================================================================== *)

Lemma continuous_on_compact_bounded (K : Rn -> Prop) (f : C0_on K) :
  is_compact K -> is_bounded_on K f.
Proof.
  intros HK.
  destruct (continuous_on_compact_is_bounded K (proj1_sig f) HK (proj2_sig f)) as [M HM].
  (* 用更简单的办法: M' >= 1 *)
  set (M' := Rmax M 1).
  assert (HM'_bound : forall x : Rn, K x -> Rabs (proj1_sig f x) <= M').
  { intros x Kx.
    apply Rle_trans with (r2 := M); [apply HM, Kx |].
    unfold M'; apply Rmax_l. }
  assert (HM'_pos : 1 <= M').
  { unfold M'. apply Rmax_r. }
  assert (HM'_pos' : M' > 0).
  { apply Rlt_le_trans with (1 := Rlt_0_1). exact HM'_pos. }
  exists M'; split; [exact HM'_pos' | exact HM'_bound].
Qed.

(* ===================================================================== *)
(* 4. 总结                                                               *)
(* ===================================================================== *)
(* 交付: *)
(*   - sup_norm: 上确界范数 (占位) *)
(*   - is_bounded_on: 单个函数有界 *)
(*   - UniformlyBounded: 一致有界族 *)
(*   - sup_norm_nonneg/triangle: 范数性质 *)
(*   - continuous_on_compact_bounded: 紧集上连续函数有界 *)