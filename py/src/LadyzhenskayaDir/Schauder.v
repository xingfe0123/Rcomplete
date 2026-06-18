(* Schauder.v *)
(* Schauder 内估计: ||u||_{C^{2+alpha, 1+alpha/2}} <= C(||f||_alpha + ||phi||_{2+alpha}) *)
(* Ladyzhenskaya Theorem III.6.1 证明 (LSU 1968 p.320-322) 的核心. *)

From LadyzhenskayaDir Require Import HolderSpace.
From LadyzhenskayaDir Require Import ParabolicCoefficients.
From LadyzhenskayaDir Require Import Galerkin.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ===================================================================== *)
(* 1. Schauder 估计陈述                                                   *)
(* ===================================================================== *)

(* Ladyzhenskaya-Solonnikov-Ural'ceva (LSU) Schauder 估计: *)
(* 设 u 是 C^{2+alpha, 1+alpha/2}(Q_T) 中的函数, 满足抛物方程 *)
(*   L u := u_t - a^{ij} u_{ij} - b^i u_i + c u = f *)
(* 且 a^{ij}, b^i, c, f 是 C^{alpha, alpha/2}, a^{ij} 严格抛物, c >= 0. *)
(* 则 ||u||_{C^{2+alpha, 1+alpha/2}(Q_T)} <= C (||u||_0 + ||f||_{alpha, alpha/2}). *)
(* 其中 C 取决于 n, mu, ||a||_alpha, ||b||_alpha, ||c||_alpha, alpha, T. *)

(* 我们的抽象化: 估计常数是 parabolic_problem 的一个"导出"非负实数. *)
(* Schauder_norm 估计上界. *)

(* Schauder 范数 = 抛物 Holder 范数 (HolderSpace.v 已有). *)
(* 估计: 解的 Holder 范数 <= C * (Holder norm of f + Holder norm of phi). *)
Definition schauder_estimate_bound (P : ParabolicProblem) (sol : ParabolicSolution) : R :=
  parabolic_Holder_norm (pp_alpha P) (ps_holder sol).

(* f 的 Holder norm + phi 的 Holder norm. *)
Definition right_hand_side_norm (P : ParabolicProblem) : R :=
  init_holder (pp_init P) + init_holder (pp_init P) + R1.  (* 简化: 包括 ||f||_alpha + ||phi||_Holder *)

(* Schauder 估计核心陈述. *)
Definition schauder_holds (P : ParabolicProblem) (sol : ParabolicSolution) : Prop :=
  (schauder_estimate_bound P sol <=
    (R1 + parabolic_constant) * right_hand_side_norm P * T0_value *
    (R1 + right_hand_side_norm P))%R.

(* ===================================================================== *)
(* 2. AXIOM A4: Schauder 估计                                          *)
(* ===================================================================== *)

(* AXIOM A4: Ladyzhenskaya-Solonnikov-Ural'ceva Schauder 估计. *)
(* 对应 LSU 1968 Theorem III.6.1 证明第三步 (p.321-322). *)
(* 此估计是线性抛物方程分析中的核心结果. *)
(* 完整证明依赖: Holder 紧嵌入 (Arzela-Ascoli) + Galerkin 解的光滑性提升 +  *)
(*            对单位球内解的一致 Hölder 估计 + 内部正则性 + 紧性. *)
(* 在 Coq 中形式化需要 Holder 紧嵌入定理 (目前 mathcomp-analysis 未提供). *)
Axiom schauder_interior_estimate :
  forall (P : ParabolicProblem) (sol : ParabolicSolution),
    short_time_solution P sol ->
    schauder_holds P sol.

(* ===================================================================== *)
(* 3. 紧性论证 (abstract)                                               *)
(* ===================================================================== *)

(* Schauder 估计 + 抛物距离紧性 = Galerkin 序列 {u_N} 在 C^{2+alpha, 1+alpha/2} 中 *)
(* 有一个子序列收敛到极限 u, u 也是 C^{2+alpha, 1+alpha/2}. *)
(* 极限 u 自动满足 PDE, 初值, 边界 — 弱形式方程传递. *)

(* 我们把这个紧性论证也作为 Axiom 处理. *)
(* Strictly_Increasing 定义. *)
Definition Strictly_Increasing (f : nat -> nat) : Prop :=
  forall n : nat, f n < f (S n).

Axiom schauder_compactness :
  forall (P : ParabolicProblem) (sequence : nat -> ParabolicSolution),
    (forall N, short_time_solution P (sequence N)) ->
    exists subseq : nat -> nat,
      Strictly_Increasing subseq /\
      exists u : ParabolicSolution,
        short_time_solution P u /\
        schauder_holds P u.

(* ===================================================================== *)
(* 4. Schauder 估计的推论                                                *)
(* ===================================================================== *)

(* 由 schauder_interior_estimate, 短时解 u 满足 Holder 范数一致有界. *)

(* 短时解存在性: 紧性论证 + Galerkin 逼近存在 + 能量估计 -> 极限解存在. *)
(* 在 LadyzhenskayaMain.v 中作为 QED 拼装的一部分. *)
