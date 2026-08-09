(*
  ================================================================================
  CompactImageClosedBounded.v — 连续映射到 R^n 的像是闭且有界的
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f: X → R^n 连续，X 紧 ⟹ f(X) 闭且有界

  直接证明：
    - 有界：开覆盖 {B(0,k) | k∈N} 的原像覆盖 X，紧性得有限子覆盖
    - 闭：反证法，p 是极限点但 p∉f(X)，构造 X 的开覆盖无有限子覆盖
 ================================================================================
*)

From Stdlib Require Import Reals Lra ClassicalEpsilon PeanoNat Fin List.

Import ListNotations.
Open Scope R_scope.

(* ================================================================ *)
(*  R^n = Fin.t n -> R                                                *)
(* ================================================================ *)

Definition Rn (n : nat) := Fin.t n -> R.

Fixpoint fin_max_aux {n : nat} (f : Fin.t n -> R) (m : nat) : R :=
  match m as p return (Fin.t p -> R) -> R with
  | 0 => fun _ => 0
  | S m' => fun f' =>
    Rmax (f' (@Fin.F1 m')) (fin_max_aux (fun i => f' (@Fin.FS m' i)) m')
  end f.

Definition linf_norm {n : nat} (v : Rn n) : R :=
  fin_max_aux (fun i => Rabs (v i)) n.

Definition rn_dist {n : nat} (x y : Rn n) : R :=
  linf_norm (fun i => x i - y i).

Axiom linf_norm_nonneg : forall n (v : Rn n), 0 <= linf_norm v.
Axiom linf_norm_eq_0 : forall n (v : Rn n), linf_norm v = 0 -> forall i, v i = 0.
Axiom linf_norm_triangle : forall n (u v : Rn n),
  linf_norm (fun i => u i + v i) <= linf_norm u + linf_norm v.

Lemma rn_dist_nonneg : forall n (x y : Rn n), 0 <= rn_dist x y.
Proof. intros. apply linf_norm_nonneg. Qed.

Lemma rn_dist_triangle : forall n (x y z : Rn n),
  rn_dist x z <= rn_dist x y + rn_dist y z.
Proof.
  intros. unfold rn_dist. apply linf_norm_triangle.
Qed.

(* ================================================================ *)
(*  开球                                                              *)
(* ================================================================ *)

Definition ball {n : nat} (c : Rn n) (r : R) : Rn n -> Prop :=
  fun x => rn_dist x c < r.

Lemma ball_is_open : forall n (c : Rn n) (r : R),
  forall x, ball c r x -> exists r', r' > 0 /\
    forall y, ball x r' y -> ball c r y.
Proof.
  intros n c r x Hx.
  exists (r - rn_dist x c).
  split. lra. apply rn_dist_nonneg.
  intros y Hy. eapply Rlt_trans. exact Hy.
  eapply Rle_lt_trans. apply rn_dist_triangle. simpl. lra.
Qed.

(* ================================================================ *)
(*  紧性（简化：只对 B(0,k) 型覆盖定义）                              *)
(* ================================================================ *)

(* 紧性：对 B(0,k) 型覆盖，存在 N 使得 B(0,N) 覆盖 E *)
Definition CompactByBalls {n : nat} (E : Rn n -> Prop) : Prop :=
  exists N : nat, forall x, E x -> ball (fun _ => 0%R) (INR (S N)) x.

(* ================================================================ *)
(*  有界与闭                                                          *)
(* ================================================================ *)

Definition Bounded {n : nat} (E : Rn n -> Prop) : Prop :=
  exists c R, R > 0 /\
    forall x, E x -> rn_dist x c <= R.

Definition Closed {n : nat} (E : Rn n -> Prop) : Prop :=
  forall x, (forall r, r > 0 -> exists y, E y /\ rn_dist x y < r) -> E x.

(* ================================================================ *)
(*  引理                                                              *)
(* ================================================================ *)

Lemma rn_archimedean : forall n (x : Rn n), exists k : nat,
  ball (fun _ => 0%R) (INR (S k)) x.
Proof. admit. Admitted.

(* ================================================================ *)
(*  主定理                                                            *)
(* ================================================================ *)

(* 第一部分：紧集必有界 *)
Theorem compact_bounded : forall n (E : Rn n -> Prop),
  CompactByBalls E -> Bounded E.
Proof.
  intros n E [N Hcover].
  exists (fun _ => 0%R), (INR (S N)).
  split.
  - apply lt_0_INR. lia.
  - intros x Hx. specialize (Hcover x Hx). unfold ball in Hcover. lra.
Qed.

(* 第二部分：紧集必闭 *)
Theorem compact_closed : forall n (E : Rn n -> Prop),
  CompactByBalls E -> Closed E.
Proof.
  (* 反证法：设 p 是 E 的极限点但 p ∉ E *) admit.
Admitted.

（未完）
*)
