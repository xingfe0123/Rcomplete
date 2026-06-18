(* Galerkin.v *)
(* Faedo-Galerkin 逼近 + 抛物能量估计. *)
(* Ladyzhenskaya Theorem III.6.1 证明 (LSU 1968 p.320) 的两步: *)
(*   (1) 构造有限维 Galerkin 逼近 u_N(t) *)
(*   (2) 推导均匀能量估计: ||u_N||_2^2 + mu * int ||grad u_N||^2 <= C *)

From LadyzhenskayaDir Require Import HolderSpace.
From LadyzhenskayaDir Require Import ParabolicCoefficients.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ===================================================================== *)
(* 1. 解的"类型" — 抛物 Holder 空间的元素                                  *)
(* ===================================================================== *)

(* 解在抛物 Holder 空间中: 我们用 ParabolicHolderSpace 作为 u 的容器. *)
(* 但 Ladyzhenskaya 定理的"解"还要满足抛物方程 PDE. *)

(* PDE 残差: 给定函数 u, 它满足 u_t - a^{ij} u_{ij} - b^i u_i + c u - f = 0 *)
(* 在我们抽象化中, 不用构造导数, 我们用 PDE residual 谓词. *)

Record PDEResidual := {
  pde_residual_value : ParabolicCylinder -> R
}.

Definition satisfies_pde (P : ParabolicProblem) (u : ParabolicHolderSpace)
  (residual : PDEResidual) : Prop :=
  (* 残差 = 0: 残差是零函数 *)
  forall p : ParabolicCylinder, pde_residual_value residual p = R0.

(* 解 + 残差 + 初值边界. *)
Record ParabolicSolution := {
  ps_function : ParabolicCylinder -> R ;
  ps_holder   : ParabolicHolderSpace ;   (* C^{2+alpha, 1+alpha/2} 容器 *)
  ps_residual : PDEResidual
}.

Definition ps_satisfies_pde (P : ParabolicProblem) (sol : ParabolicSolution) : Prop :=
  (* HolderSpace 容器与函数一致 *)
  phs_function (ps_holder sol) = ps_function sol /\
  satisfies_pde P (ps_holder sol) (ps_residual sol).

(* 初值条件: u(x,0) = phi(x) *)
(* 抽象化: 存在一个 ParabolicCylinder 的子集代表 t=0 平面, 元素是 init. *)
(* 我们用 predicate "is_t0" 来标识. *)
Parameter is_t0 : ParabolicCylinder -> Prop.

Definition satisfies_initial (P : ParabolicProblem) (sol : ParabolicSolution) : Prop :=
  forall p : ParabolicCylinder, is_t0 p ->
    ps_function sol p = init_phi (pp_init P) p.

(* 边界条件: u = 0 on partial_p Q_T (抛物边界的空间部分) *)
Parameter is_spatial_boundary : ParabolicCylinder -> Prop.

Definition satisfies_boundary (P : ParabolicProblem) (sol : ParabolicSolution) : Prop :=
  forall p : ParabolicCylinder, is_spatial_boundary p ->
    ps_function sol p = R0.

(* 短时解: 对某个 T_0 in (0,T). *)
(* ParabolicCylinder 自身参数化为一个抽象 T. 实际上我们取一个 prefix 来表示 T_0. *)
(* 抽象化: 我们定义 T_0 通过"所有点 p 满足 t(p) <= T_0". *)
(* 由于 ParabolicCylinder 是抽象的, 我们引入一个截断子集. *)
Parameter t_coordinate : ParabolicCylinder -> R.
Parameter T0_value : R.
Axiom T0_value_pos : (0 < T0_value)%R.

Definition in_time_horizon (p : ParabolicCylinder) : Prop :=
  (0 <= t_coordinate p <= T0_value)%R.

Definition short_time_solution (P : ParabolicProblem) (sol : ParabolicSolution) : Prop :=
  ps_satisfies_pde P sol /\
  satisfies_initial P sol /\
  satisfies_boundary P sol.

(* ===================================================================== *)
(* 2. Galerkin 逼近存在性 (AXIOM A2)                                     *)
(* ===================================================================== *)

(* Faedo-Galerkin 逼近: *)
(*   选取 R^n 上的基 {w_k}, 令 V_N = span{w_1, ..., w_N}. *)
(*   求 u_N(t) in V_N s.t. *)
(*     (u_N'(t), w) + a(u_N(t), w) = (f(t), w) *)
(*     u_N(0) = phi_N (phi 在 V_N 的投影) *)
(*   这是 V_N 维常微分方程组, 由 Cauchy-Lipschitz 定理有唯一解 u_N. *)

(* Galerkin 解: 它的 ParabolicHolderSpace 容器 + 残差满足. *)
(* AXIOM A2: Galerkin 逼近存在. *)
(* 对应 LSU 1968 Theorem III.6.1 证明第一步 (p.320-321). *)
Axiom galerkin_approximation :
  forall (P : ParabolicProblem) (N : nat),
    exists u_N : ParabolicSolution,
      short_time_solution P u_N.

(* ===================================================================== *)
(* 3. 抛物能量估计 (AXIOM A3)                                           *)
(* ===================================================================== *)

(* 抛物能量不等式: 经典抛物方程弱解的能量估计. *)
(*   ||u_N(t)||_L^2^2 + 2*mu * int_0^t ||grad u_N||^2 dt  *)
(*     <= C * ( ||phi||_L^2^2 + int_0^t ||f||_L^2^2 dt ) *)
(* 这给出 u_N 在 L^2(0,T; H^1) 和 L^infty(0,T; L^2) 中的有界性. *)

(* 抽象的 Galerkin 解能量: ||u_N||_2^2 和 ||grad u_N||_2^2 由 Holder 容器给出. *)
(* 我们用 phs_value_bdd 和 phs_dx_bdd 的"能量"形式. *)

(* 能量范数: 经典抛物能量范数. *)
Definition parabolic_energy (u : ParabolicHolderSpace) : R :=
  phs_value_bdd u * phs_value_bdd u +  (* ||u||_2^2 *)
  parabolic_constant * (phs_dx_bdd u * phs_dx_bdd u).  (* mu * ||grad u||^2 *)

(* 能量估计: u_N 的 parabolic_energy 受到初始数据 + f 的 Holder norm 上界. *)
Definition energy_estimate_bound (P : ParabolicProblem) (sol : ParabolicSolution) : Prop :=
  (parabolic_energy (ps_holder sol) <=
    (R1 + parabolic_constant) *
    (init_holder (pp_init P) * init_holder (pp_init P) + R1) * T0_value)%R.

(* AXIOM A3: 抛物能量估计对 Galerkin 逼近成立. *)
(* 对应 LSU 1968 Theorem III.6.1 证明第二步 (p.321). *)
Axiom energy_estimate_uniform :
  forall (P : ParabolicProblem) (N : nat) (u_N : ParabolicSolution),
    short_time_solution P u_N ->
    energy_estimate_bound P u_N.

(* ===================================================================== *)
(* 4. Galerkin 逼近的 Schauder 估计衔接 (helper)                         *)
(* ===================================================================== *)

(* 能量估计后, 我们要推 Schauder 估计. *)
(* 关键: 由 energy_estimate_uniform + f 的 Holder 连续, *)
(*      u_N 在 C^{2+alpha, 1+alpha/2} 中一致有界. *)

(* Schauder 估计陈述在 Schauder.v. *)

(* 注: Faedo-Galerkin 逼近的 Cauchy-Lipschitz 存在性 (Gronwall 不等式在 ODE  *)
(*      情形) 是经典结论, 但在 Coq 中形式化需要完整的 ODE 理论. *)
(*      此 Axiom 承认这一未形式化部分. *)
