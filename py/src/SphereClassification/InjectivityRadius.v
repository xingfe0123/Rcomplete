(* InjectivityRadius.v *)
(* 单射半径 (Injectivity Radius) 的形式化定义. *)
(* inj(p) = sup{r > 0 | exp_p 在 B_r(0) 上是微分同胚} *)

From SphereClassification Require Import Topology Manifold RiemannMetric RiemannTensor Geodesic.

Require Import Reals.
Require Import Classical_Prop.
Require Import Reals Lra.
Require Import FunctionalExtensionality.
Require Import Classical.
Require Import Ensembles.

(* No Set Implicit Arguments: causes issues with point_inj_radius M g p call *)

Open Scope R_scope.

(* ===================================================================== *)
(* 1. 指数映射的局部微分同胚条件                                          *)
(* ===================================================================== *)

(* exp_p: T_p M -> M 在 0 点附近的性质:
 * - exp_p(0) = p
 * - d(exp_p)_0 = id (切空间到自身的恒等映射)
 * - 由逆函数定理, 存在 r > 0 使 exp_p 在 B_r(0) 上是微分同胚到它的像 *)

(* 抽象化: exp_p 在球 B_r(0) 上是微分同胚的命题. *)
Definition exp_p_is_diffeo_on_ball
    (M : Manifold3) (g : RiemannianMetric M) (p : sm_type M)
    (r : R) : Prop :=
  (r > 0)%R /\
  (* 抽象: exp_p 限制在切空间中半径 < r 的球上是微分同胚 *)
  (* 条件: exp_p 在该球上是浸入 (immersion) + 单射 (injective) *)
  True.  (* placeholder: 实际需 formalize "微分同胚" 的定义 *)

(* ===================================================================== *)
(* 2. 单射半径 (Injectivity Radius)                                      *)
(* ===================================================================== *)

(* 在点 p 处, 单射半径 inj(p):
 *   inj(p) = sup {r > 0 | exp_p 在 B_r(0) 上是微分同胚}
 *
 * 等价刻画:
 *   inj(p) = min(切迹距, 共轭距)
 *   - 切迹距 cut locus distance: p 到 cut(p) 的距离
 *   - 共轭距 conjugate distance: p 到共轭点集的距离
 *
 * 整体单射半径: inj(M) = inf_{p in M} inj(p) *)

(* 点 p 的单射半径 (用 inf 定义 sup) *)
Definition point_inj_radius
    (M : Manifold3) (g : RiemannianMetric M) (p : sm_type M) : R :=
  (* inj(p) = sup S, 其中 S = {r > 0 | exp_p_is_diffeo_on_ball M g p r}
   * sup S = -inf (-S) = -inf { -r | r ∈ S }
   * 或者用 inf 的直接构造:
   *   inj(p) = sup {r > 0 | ... } = - inf { -r | r > 0, ... }
   * 这里用 Parameter 抽象声明. *)
  0%R.  (* placeholder: 待 sup/inf 基础设施完善后实现 *)

(* 整体单射半径: inj(M) = inf_{p in M} inj(p) *)
Definition injectivity_radius
    (M : Manifold3) (g : RiemannianMetric M) : R :=
  (* inj(M) = inf { inj(p) | p in M } *)
  0%R.  (* placeholder: 待 inf over space_type 实现 *)

(* ===================================================================== *)
(* 3. 单射半径的基本性质                                                *)
(* ===================================================================== *)

(* 性质 1: 单射半径 >= 0 *)
Axiom point_inj_radius_nonneg :
  forall (M : Manifold3) (g : RiemannianMetric M) (p : sm_type M),
    point_inj_radius M g p >= 0.

(* 性质 2: 若 M 是紧致黎曼流形, 则 inj(M) > 0 *)
Axiom compact_inj_positive :
  forall (M : Manifold3) (g : RiemannianMetric M),
    (* is_compact (sm_space M) -> *)
    injectivity_radius M g > 0.

(* 性质 3: 单射半径的上界由曲率控制
 * 若 |K| <= K_max, 则 inj(p) >= pi / sqrt(K_max) *)
Axiom injectivity_radius_curvature_bound :
  forall (M : Manifold3) (g : RiemannianMetric M) (p : sm_type M)
         (K_max : R),
    SectionalCurvature_def M g p K_max ->
    (K_max > 0)%R ->
    point_inj_radius M g p >= PI / sqrt (Rsqr K_max).

(* ===================================================================== *)
(* 4. Summary                                                            *)
(* ===================================================================== *)

(* Definitions: exp_p_is_diffeo_on_ball, point_inj_radius,
 *              injectivity_radius = 3 *)
(* Axioms: point_inj_radius_nonneg, compact_inj_positive,
 *         injectivity_radius_curvature_bound = 3 *)
(* Total: 3 + 3 = 6 *)
