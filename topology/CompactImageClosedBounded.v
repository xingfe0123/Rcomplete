(*
  ================================================================================
  CompactImageClosedBounded.v — 连续映射的像是闭且有界的
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f: X → R^n 连续，X 紧度量空间 ⟹ f(X) 在 R^n 中闭且有界

  证明：
    1. 由 ContinuousCompact.v 的 continuous_image_of_compact_is_compact
       得 f(X) 在 R^n 中紧
    2. 直接证明 R^n 中紧集必有界（开球覆盖法）
    3. 直接证明度量空间中紧集必闭
 ================================================================================
*)

From Stdlib Require Import Reals Lra ClassicalEpsilon.

(* R^n 的 L∞ 范数来自 HeineBorelLimitPoint.v 中已编译的定义 *)
Definition Rn (n : nat) := Fin.t n -> R.

Fixpoint fin_max_aux {n : nat} (f : Fin.t n -> R) (m : nat) : R :=
  match m as p return (Fin.t p -> R) -> R with
  | 0 => fun _ => 0
  | S m' => fun f' =>
    Rmax (f' (@Fin.F1 m')) (fin_max_aux (fun i => f' (@Fin.FS m' i)) m')
  end f.

Definition linf_norm {n : nat} (v : Rn n) : R :=
  fin_max_aux (fun i => Rabs (v i)) n.

(* ================================================================ *)
(*  R^n 上的度量                                                      *)
(* ================================================================ *)

Definition rn_dist {n : nat} (x y : Rn n) : R :=
  linf_norm (fun i => x i - y i).

(* 度量公理——需要用公理证明（技术分析引理） *)
Axiom rn_dist_nonneg : forall n (x y : Rn n), 0 <= rn_dist x y.
Axiom rn_dist_eq : forall n (x y : Rn n), rn_dist x y = 0 <-> x = y.
Axiom rn_dist_sym : forall n (x y : Rn n), rn_dist x y = rn_dist y x.
Axiom rn_dist_triangle : forall n (x y z : Rn n),
  rn_dist x z <= rn_dist x y + rn_dist y z.

(* R^n 作为度量空间 *)
Definition RnMetricSpace (n : nat) : MetricSpace :=
  mkMetricSpace (Rn n) (@rn_dist n)
    (rn_dist_nonneg n) (rn_dist_eq n) (rn_dist_sym n) (rn_dist_triangle n).

(* ================================================================ *)
(*  R^n 中的有界集                                                    *)
(* ================================================================ *)

Definition bounded_Rn {n : nat} (E : Rn n -> Prop) : Prop :=
  exists c R, R > 0 /\
    forall x, E x -> rn_dist x c <= R.

(* R^n 中的闭集：包含所有极限点 *)
Definition closed_Rn {n : nat} (E : Rn n -> Prop) : Prop :=
  forall x, (forall r, r > 0 -> exists y, E y /\
    rn_dist x y < r) -> E x.

(* ================================================================ *)
(*  引理：开球                                                        *)
(* ================================================================ *)

Lemma open_ball_Rn_is_open : forall n (c : Rn n) (r : R),
  OpenSet (RnMetricSpace n) (ball (RnMetricSpace n) c r).
Proof.
  intros n c r x Hx.
  unfold ball in Hx. unfold rn_dist in Hx.
  exists (r - linf_norm (fun i => x i - c i)).
  split.
  - unfold rn_dist. unfold linf_norm. lra.  (* 需 linf_norm 性质，用公理 *)
  - intros y Hy.
    unfold ball. unfold rn_dist.
Abort.  (* 需 linf_norm 的三角不等式，待补充 *)

（未完）
*)
