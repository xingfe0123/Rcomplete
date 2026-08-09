(*
  ================================================================================
  Vec.v — R^n 向量类型定义（Fin.t n -> R）
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定义 Vec n = Fin.t n -> R 及其基本运算。
  ================================================================================
*)

From Stdlib Require Import Reals List Lra Lia.
From Stdlib Require Fin.

Open Scope R_scope.

(* ================================================================ *)
(*  类型定义                                                          *)
(* ================================================================ *)

Definition Vec (n : nat) := Fin.t n -> R.

(* ================================================================ *)
(*  基本运算                                                          *)
(* ================================================================ *)

(* 零向量 *)
Definition vec_zero {n : nat} : Vec n := fun _ => 0%R.

(* 向量加法 *)
Definition vec_add {n : nat} (u v : Vec n) : Vec n :=
  fun i => (u i + v i)%R.

(* 向量减法 *)
Definition vec_sub {n : nat} (u v : Vec n) : Vec n :=
  fun i => (u i - v i)%R.

(* 标量乘法 *)
Definition vec_smul {n : nat} (c : R) (u : Vec n) : Vec n :=
  fun i => (c * u i)%R.

(* 向量取反 *)
Definition vec_neg {n : nat} (u : Vec n) : Vec n :=
  fun i => (- u i)%R.

(* ================================================================ *)
(*  L∞ 范数（最大值范数）                                            *)
(* ================================================================ *)

(* 对 Fin.t n 求 max 的辅助函数 *)
Fixpoint fin_max_aux {n : nat} (f : Fin.t n -> R) {struct n} : R :=
  match n as p return (Fin.t p -> R) -> R with
  | 0 => fun _ => 0%R
  | S n' => fun f' => Rmax (f' (@Fin.F1 n')) (fin_max_aux (fun i => f' (@Fin.FS n' i)))
  end f.

Definition fin_max (n : nat) (f : Fin.t n -> R) : R :=
  @fin_max_aux n f.

(* L∞ 范数 *)
Definition vec_linf_norm {n : nat} (v : Vec n) : R :=
  fin_max n (fun i => Rabs (v i)).

(* ================================================================ *)
(*  度量                                                              *)
(* ================================================================ *)

(* L∞ 度量 *)
Definition vec_linf_dist {n : nat} (u v : Vec n) : R :=
  vec_linf_norm (vec_sub u v).

Close Scope R_scope.
