(* ============================================================================ *)
(*  R3Model.v                                                                   *)
(*  ℝ³ 向量代数公共模块                                                         *)
(*                                                                            *)
(*  提供 3D 欧氏模型共享的基础定义:                                             *)
(*    V3, Point, coord_x/y/z, vadd, vsub, vscale, vzero, dot,                  *)
(*    norm2, dist2                                                              *)
(*                                                                            *)
(*  使用者: Model_Consistency.v, III5_Independence.v, IV_Independence.v          *)
(* ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

(* ---- ℝ³ 类型 ---- *)
Definition V3 : Type := R * R * R.
Definition Point : Type := V3.

(* ---- 坐标投影 ---- *)
Definition coord_x (p : V3) : R := fst (fst p).
Definition coord_y (p : V3) : R := snd (fst p).
Definition coord_z (p : V3) : R := snd p.

(* ---- 向量运算 ---- *)
Definition vadd (u v : V3) : V3 :=
  (fst (fst u) + fst (fst v), snd (fst u) + snd (fst v), snd u + snd v).

Definition vsub (u v : V3) : V3 :=
  (fst (fst u) - fst (fst v), snd (fst u) - snd (fst v), snd u - snd v).

Definition vscale (t : R) (v : V3) : V3 :=
  (t * fst (fst v), t * snd (fst v), t * snd v).

Definition vzero : V3 := (0, 0, 0).

(* ---- 点积与范数 ---- *)
Definition dot (u v : V3) : R :=
  fst (fst u) * fst (fst v) + snd (fst u) * snd (fst v) + snd u * snd v.

Definition norm2 (v : V3) : R := dot v v.
Definition dist2 (A B : V3) : R := let d := vsub A B in dot d d.

Lemma norm2_nonneg : forall v : V3, 0 <= norm2 v.
Proof.
  intros [[x y] z]; unfold norm2, dot; simpl.
  apply Rplus_le_le_0_compat; [apply Rplus_le_le_0_compat|]; apply Rle_0_sqr.
Qed.
