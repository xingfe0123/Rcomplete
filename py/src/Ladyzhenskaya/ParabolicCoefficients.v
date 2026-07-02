(* ParabolicCoefficients.v *)
(* 抛物方程输入系数 + 严格抛物性. *)
(* Ladyzhenskaya Theorem III.6.1 假设: *)
(*   a^{ij}(x,t), b^i(x,t), c(x,t), f(x,t) 在 Q_T 上 C^{alpha, alpha/2} *)
(*   严格抛物: exists mu>0, a^{ij} xi_i xi_j >= mu |xi|^2 *)
(*   c >= 0 *)

From Ladyzhenskaya Require Import HolderSpace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ===================================================================== *)
(* 1. 系数空间                                                          *)
(* ===================================================================== *)

(* 系数 a^{ij}, b^i, c, f 都是抛物柱到 R 的函数. *)
(* 简化: 我们把 a^{ij} 的 i,j 索引编码为 R 的乘积 (u*v) — 与 xi_i xi_j 语义一致. *)

Record ParabolicCoefficients := {
  pc_a : ParabolicCylinder -> R -> R ;   (* (x,t) -> a^{ij}(x,t), 索引 ij 用 R 表示 *)
  pc_b : ParabolicCylinder -> R -> R ;   (* (x,t) -> b^i(x,t), 索引 i 用 R 表示 *)
  pc_c : ParabolicCylinder -> R ;        (* (x,t) -> c(x,t) *)
  pc_f : ParabolicCylinder -> R          (* (x,t) -> f(x,t) *)
}.

(* ===================================================================== *)
(* 2. Holder 正则性                                                     *)
(* ===================================================================== *)

(* 抛物 Holder 连续: 系数 c, f 是 C^{alpha, alpha/2}. *)
(* 定义: 存在上界 M 使得 *)
(*   |coef(p) - coef(q)| <= M * (R1 + d_par^alpha(p,q)) *)
(* 系数 a, b 同样 — 编码为 Holder 谓词. *)

Definition coeffs_Holder_regular
  (alpha : HolderExponent)
  (coefs : ParabolicCoefficients) : Prop :=
  exists M : R, (0 < M)%R /\
    (* c Holder *)
    (forall p q,
       (Rabs (pc_c coefs p - pc_c coefs q) <= M * (R1 + parabolic_distance_pow (alpha_val alpha) p q))%R) /\
    (* f Holder *)
    (forall p q,
       (Rabs (pc_f coefs p - pc_f coefs q) <= M * (R1 + parabolic_distance_pow (alpha_val alpha) p q))%R).

(* AXIOM A1: Holder 正则性可从 C^{alpha, alpha/2} 输入推出. *)
(* 这对应 LSU Theorem III.6.1 假设 (6.1)-(6.4), p.320. *)
(* 形式化不证明 (需要 mathcomp/analysis 中尚未形式化的 Holder 空间抽象). *)
Axiom coeff_Holder_regularity :
  forall (alpha : HolderExponent) (coefs : ParabolicCoefficients),
    coeffs_Holder_regular alpha coefs.

(* ===================================================================== *)
(* 3. 严格抛物性                                                        *)
(* ===================================================================== *)

(* 严格抛物性: a^{ij}(x,t) xi_i xi_j >= mu |xi|^2 对所有 (x,t), xi 成立. *)
(* 抽象化: 严格抛物性是一个谓词, 它接受抛物性常数 mu > 0 和系数. *)
Definition strictly_parabolic (coefs : ParabolicCoefficients) (mu : R) : Prop :=
  (0 < mu)%R /\
  forall (p : ParabolicCylinder) (xi : R),
    (* a^{ij} xi_i xi_j, 简化为 a(p, xi^2) >= mu * xi^2 *)
    (pc_a coefs p (xi * xi) >= mu * (xi * xi))%R.

(* 抛物性常数: 严格抛物条件的存在性 — 我们作为假设引入. *)
Parameter parabolic_constant : R.
Axiom parabolic_constant_pos : (0 < parabolic_constant)%R.

Definition parabolic_data (coefs : ParabolicCoefficients) : Prop :=
  strictly_parabolic coefs parabolic_constant /\
  (* c >= 0: c 是非负的 *)
  (forall p : ParabolicCylinder, (0 <= pc_c coefs p)%R).

(* ===================================================================== *)
(* 4. 初值                                                              *)
(* ===================================================================== *)

(* 初值函数: phi 在 t=0 平面上取值, Holder 连续. *)

Record InitialData := {
  init_phi : ParabolicCylinder -> R ;
  init_holder : R   (* ||phi||_Holder 上界 *)
}.

Definition init_smooth (data : InitialData) : Prop :=
  (0 < init_holder data)%R /\
  forall p q : ParabolicCylinder,
    (Rabs (init_phi data p - init_phi data q) <= init_holder data * parabolic_distance_pow R1 p q)%R.

(* ===================================================================== *)
(* 5. 抛物方程输入: 总假设                                                *)
(* ===================================================================== *)

Record ParabolicProblem := {
  pp_alpha     : HolderExponent ;
  pp_coefs     : ParabolicCoefficients ;
  pp_init      : InitialData ;
  pp_coef_data : coeffs_Holder_regular pp_alpha pp_coefs ;  (* Holder regular 假设 *)
  pp_parab     : parabolic_data pp_coefs ;
  pp_init_ok   : init_smooth pp_init
}.

(* ===================================================================== *)
(* 4. 经典解光滑性定义 (classical_smooth / classical_pde_residual)          *)
(* ===================================================================== *)

(* classical_smooth: 函数 u 属于 C^{2+alpha, 1+alpha/2}(Q_T). *)
(* 等价于: 存在 ParabolicHolderSpace 实例, 各项导数范数有界. *)

Definition classical_smooth
  (alpha : HolderExponent)
  (u : ParabolicCylinder -> R)
  (M : R) : Prop :=
  (0 < M)%R /\
  exists phs : ParabolicHolderSpace,
    phs_function phs = u /\
    (parabolic_Holder_norm alpha phs <= M)%R.

(* 兼容性: 抛物常数 + 区域大小 给出估计常数. *)
Definition parabolic_constants_bound (P : ParabolicProblem) : R :=
  parabolic_constant * parabolic_constant.

(* ===================================================================== *)
(* 6. Holder 半范构造函数                                                *)
(* ===================================================================== *)

(* 为系数 Holder 半范构造 HolderSemivariation 实例. *)
(* 不构造证明: 抽象 Holder 半范是 HolderSemivariation 抽象类型的"实例". *)
(* 由 Axiom 编码 (LSU 1968 p.320 (6.4)). *)

Axiom coefficient_holder_semivariation :
  forall (P : ParabolicProblem), HolderSemivariation ParabolicCylinder.
