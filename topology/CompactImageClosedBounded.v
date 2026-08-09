(*
  ================================================================================
  CompactImageClosedBounded.v — 连续映射到 R^n 的像是闭且有界的
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f: X → R^n 连续，X 紧 ⟹ f(X) 闭且有界
 ================================================================================
*)

From Stdlib Require Import Reals Lra ClassicalEpsilon PeanoNat Fin List.

Import ListNotations.
Open Scope R_scope.

(* ================================================================ *)
(*  R^n = Fin.t n -> R                                                *)
(* ================================================================ *)

Definition Rn (n : nat) := FinT n -> R.

Inductive FinT : nat -> Set :=
  | F1 : forall n : nat, FinT (S n)
  | FS : forall n : nat, FinT n -> FinT (S n).

Fixpoint fin_max_aux {n : nat} (f : FinT n -> R) (m : nat) : R :=
  match m as p return (FinT p -> R) -> R with
  | 0 => fun _ => 0
  | S m' => fun f' =>
    Rmax (f' (@F1 m')) (fin_max_aux (fun i => f' (@FS m' i)) m')
  end f.

Definition linf_norm {n : nat} (v : Rn n) : R :=
  fin_max_aux (fun i => Rabs (v i)) n.

Definition vsub {n : nat} (u v : Rn n) : Rn n := fun i => (u i - v i)%R.
Definition rn_dist {n : nat} (x y : Rn n) : R := linf_norm (vsub x y).

Axiom linf_norm_nonneg : forall n (v : Rn n), 0 <= linf_norm v.
Axiom linf_norm_triangle : forall n (u v : Rn n),
  linf_norm (vsub u v) <= linf_norm u + linf_norm v.

Lemma rn_dist_nonneg : forall n (x y : Rn n), 0 <= rn_dist x y.
Proof. intros. apply linf_norm_nonneg. Qed.

Lemma rn_dist_triangle : forall n (x y z : Rn n),
  rn_dist x z <= rn_dist x y + rn_dist y z.
Proof. intros. unfold rn_dist. apply linf_norm_triangle. intros i. lra. Qed.

(* ================================================================ *)
(*  开球                                                              *)
(* ================================================================ *)

Definition open_ball {n : nat} (c : Rn n) (r : R) : Rn n -> Prop :=
  fun x => rn_dist x c < r.

Lemma open_ball_is_open : forall n (c : Rn n) (r : R),
  forall x, open_ball c r x -> exists r', r' > 0 /\
    forall y, open_ball x r' y -> open_ball c r y.
Proof.
  intros n c r x Hx.
  exists (r - rn_dist x c).
  split. lra. apply rn_dist_nonneg.
  intros y Hy. eapply Rlt_trans. exact Hy.
  eapply Rle_lt_trans. apply rn_dist_triangle. simpl. lra.
Qed.

(* ================================================================ *)
(*  紧性（简化定义：对 B(0,k) 型覆盖存在统一的上界 N）               *)
(* ================================================================ *)

(* 简化定义：紧 = 有界（这是错误的！但对于 R^n 的子集，紧 ⟺ 闭且有界）
   这里我们直接用正确的定义 *)

Definition OpenSet {n : nat} (U : Rn n -> Prop) : Prop :=
  forall x, U x -> exists r, r > 0 /\
    forall y, open_ball x r y -> U y.

Definition Compact {n : nat} (E : Rn n -> Prop) : Prop :=
  (* 对任意开集族 F，如果 F 覆盖 E，则存在 F 的有限子族也覆盖 E *)
  forall (F : nat -> Rn n -> Prop),
    (forall k, OpenSet (F k)) ->
    (forall x, E x -> exists k, F k x) ->
    exists N : nat, forall x, E x -> exists k, (k < N)%nat /\ F k x.

（上面这个定义用了 nat 索引的开集族，更方便）
*)

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
  open_ball (fun _ => 0%R) (INR (S k)) x.
Proof. admit. Admitted.

(* ================================================================ *)
(*  紧集必有界                                                        *)
(* ================================================================ *)

Theorem compact_bounded : forall n (E : Rn n -> Prop),
  Compact E -> Bounded E.
Proof.
  intros n E Hcompact.
  apply rn_archimedean.
  （思路：用 F(k) = B(0, k+1) 作为开覆盖，紧性给出 N）
*)

（未完——需完整写出）
*)
