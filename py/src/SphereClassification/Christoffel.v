(* Christoffel.v *)
(* Christoffel 符号: Gamma^k_ij — Levi-Civita 联络的坐标表示. *)
(* 依赖: RiemannMetric (提供度量 g), R3 (提供指标类型). *)
(* 风格: Parameter + Axiom, 与 SphereClassification 一致. *)
(* 注意: 使用 @f 显式参数化以避免 Coq 对 (forall M, RiemannianMetric M -> ...)
   类型推断的歧义 (已知 Coq 8.18 编译器的依赖类型问题). *)

From SphereClassification Require Import Manifold RiemannMetric.

Require Import Reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(* ===================================================================== *)
(* Christoffel 符号 (Levi-Civita 联络)                                       *)
(* ===================================================================== *)

(* Christoffel 符号 Gamma^k_ij: 三个指标, 上标 k, 下标 i, j. *)
(* 抽象化: 用 R3 表示指标三元组 (i,j,k). *)
(* Gamma^k_ij(p, g) 是流形点 p 处度量 g 的 Christoffel 符号. *)
(* 第一个参数是 Manifold3, 第二个是 RiemannianMetric M (隐式参数化). *)

Parameter christoffel_symbols :
  forall (M : Manifold3) (g : RiemannianMetric M), Manifold3 -> R3 -> R.
(* christoffel_symbols M g p (i,j,k) = Gamma^k_ij(p) *)

(* ===================================================================== *)
(* Christoffel 符号对称性                                                    *)
(* ===================================================================== *)

(* Gamma^k_ij = Gamma^k_ji (无挠联络, Levi-Civita 性质) *)
Axiom christoffel_symmetry :
  forall (M : Manifold3) (g : RiemannianMetric M) p idx,
    @christoffel_symbols M g p idx =
    @christoffel_symbols M g p (snd (fst idx), fst (fst idx), snd idx).

(* ===================================================================== *)
(* 第一 Bianchi 恒等式 (抽象占位)                                            *)
(* ===================================================================== *)

(* R^l_ijk + R^l_jki + R^l_kij = 0 *)
(* 作为经典定理保留, 依赖 Riemann 曲率张量. *)

(* ===================================================================== *)
(* 协变导数                                                                 *)
(* ===================================================================== *)

(* 向量场 V 沿方向 d_i 的协变导数: (nabla_i V)^k = d_i V^k + Gamma^k_ij V^j *)
(* 抽象化: covariant_derivative 是一个参数化操作. *)

Parameter covariant_derivative :
  forall (M : Manifold3) (g : RiemannianMetric M),
    Manifold3 -> R3 -> R -> R.
(* covariant_derivative M g p idx V = (nabla_idx V)(p) *)

(* ===================================================================== *)
(* Lie 导数                                                                 *)
(* ===================================================================== *)

(* 向量场 X 对度量 g 的 Lie 导数: (L_X g)_ij = nabla_i X_j + nabla_j X_i *)
(* 抽象化: lie_derivative_metric 是一个参数化操作. *)

Parameter lie_derivative_metric :
  forall (M : Manifold3) (g : RiemannianMetric M),
    Manifold3 -> R -> R.
(* lie_derivative_metric M g p X = (L_X g)(p) *)

(* ===================================================================== *)
(* 依赖总结                                                                 *)
(* ===================================================================== *)

(* Parameters: christoffel_symbols, covariant_derivative, lie_derivative_metric = 3 *)
(* Axioms: christoffel_symmetry = 1 *)
(* 所有 Axiom 使用 @f 显式传参以绕过 Coq 8.18 的依赖类型推断问题. *)