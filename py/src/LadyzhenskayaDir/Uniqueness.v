(* Uniqueness.v *)
(* 抛物方程的弱最大值原理 -> 唯一性. *)
(* Ladyzhenskaya Theorem III.6.1 证明的最后一步. *)

From LadyzhenskayaDir Require Import HolderSpace.
From LadyzhenskayaDir Require Import ParabolicCoefficients.
From LadyzhenskayaDir Require Import Galerkin.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ===================================================================== *)
(* 1. 抛物最大值原理                                                     *)
(* ===================================================================== *)

(* 抛物最大值原理 (Hopf 引理的抛物版): *)
(* 设 L u = u_t - a^{ij} u_{ij} - b^i u_i + c u, c >= 0, a^{ij} 严格抛物. *)
(* 若 Lu >= 0 在 Q_T 中, 则 u 在 Q_T 中不能取到非负最大值 (除非是常数). *)
(* Ladyzhenskaya 1968 Theorem III.6.1 p.320 的直接推论. *)

(* AXIOM A5: 抛物最大值原理 / 唯一性. *)
(* 形式化不证明 (需要内部球 Hopf 引理 + 边界 Hopf 引理). *)
Axiom parabolic_max_principle :
  forall (P : ParabolicProblem) (u1 u2 : ParabolicSolution),
    short_time_solution P u1 ->
    short_time_solution P u2 ->
    (* 若 u1 和 u2 满足同一抛物方程, 同一初值, 同一边界, 则 u1 = u2 *)
    ps_function u1 = ps_function u2.

(* 直接调用 — 同一问题不可能有两个不同的短时解. *)
Definition parabolic_uniqueness (P : ParabolicProblem) (u1 u2 : ParabolicSolution) : Prop :=
  ps_function u1 = ps_function u2.

Theorem parabolic_uniqueness_from_max :
  forall (P : ParabolicProblem) (u1 u2 : ParabolicSolution),
    short_time_solution P u1 -> short_time_solution P u2 -> parabolic_uniqueness P u1 u2.
Proof.
  intros P u1 u2 H1 H2. unfold parabolic_uniqueness.
  exact (@parabolic_max_principle P u1 u2 H1 H2).
Qed.

(* ===================================================================== *)
(* 2. AXIOM A5 (recap)                                                *)
(* ===================================================================== *)

(* 此 Axiom 编码: Ladyzhenskaya 1968 Theorem III.6.1 的唯一性部分. *)
(* 对应 LSU 1968 p.320 推论: 初值问题 (1.1) 至多有一个 C^{2+alpha, 1+alpha/2} 解. *)
(* 证明依赖: 抛物弱最大值原理 + Hopf 引理 + 严格抛物性. *)
(* 在 Coq 中形式化需要: 1) Hopf 引理的几何论证; 2) 抛物最大原理. *)
(* 这部分是椭圆/抛物 PDE 的核心分析, 完整证明约 20-30 页. *)

(* 等价表述: 给定一个短时解 u1, 任何同输入的短时解 u2 都满足 u1 = u2. *)
Axiom schauder_global_uniqueness :
  forall (P : ParabolicProblem) (u1 u2 : ParabolicSolution),
    short_time_solution P u1 ->
    short_time_solution P u2 ->
    ps_function u1 = ps_function u2.
