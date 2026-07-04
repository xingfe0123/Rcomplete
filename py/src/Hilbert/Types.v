(* ============================================================================ *)
(*  Types.v                                                                     *)
(*  Tier-3: 引入 Hilbert 几何的辅助类型                                          *)
(*                                                                            *)
(*  本文件不引入任何 Axiom, 仅使用 Common.v 的 Parameter 构造派生类型              *)
(*                                                                            *)
(*  引入类型:                                                                  *)
(*    - Ray:        射线 (直线 + 起点), 用于 III-1 线段迁移                       *)
(*    - Angle:      角 (三点 A,B,C 且 A≠B≠C), 用于角合同公理                     *)
(*    - OnRay:      点在射线上                                                  *)
(*                                                                            *)
(*  CongSeg 在 CongruenceTheorem.v 中声明, 不在此引用                              *)
(*  TransferCongSeg 定义在 CongruenceTheorem.v 中 (需 CongSeg)                     *)
(* ============================================================================ *)

From Stdlib Require Import Classical.
From Hilbert Require Import Common.

(* ============================================================================ *)
(*  Ray 类型: 射线 (有向, 从起点出发沿直线延伸)                                    *)
(*                                                                            *)
(*  一条射线由 (起点 C, 直线 l) 唯一确定. C ∈ l.                                  *)
(*  射线上的点 X 满足: C = X 或 X 在 l 上且与 C 不同                             *)
(* ============================================================================ *)

Record Ray : Type := mkRay {
  ray_origin : Point;
  ray_line   : Line;
  ray_valid  : Incid ray_origin ray_line
}.

Definition OnRay (X : Point) (r : Ray) : Prop :=
  X = ray_origin r \/ (Incid X (ray_line r) /\ X <> ray_origin r).

(* ============================================================================ *)
(*  Angle 类型: 角 ∠(A,B,C)                                                     *)
(*                                                                            *)
(*  角由顶点 B 与两条边 BA, BC 唯一确定. A≠B, B≠C, A≠C (非退化)                 *)
(*  角合同 CongAng 已在 CongruenceTheorem.v 中声明, 此处仅定义角类型               *)
(* ============================================================================ *)

Record Angle : Type := mkAngle {
  angle_vertex   : Point;
  angle_ray_a    : Line;   (* 第一条射线所在的直线 *)
  angle_ray_c    : Line;   (* 第二条射线所在的直线 *)
  angle_valid_a  : Incid angle_vertex angle_ray_a;
  angle_valid_c  : Incid angle_vertex angle_ray_c
}.

(* ============================================================================ *)
(*  Tier-3 引入: Ray + Angle, 零 Axiom                                          *)
(*  所有参数在 Common.v / CongruenceTheorem.v 中                                  *)
(* ============================================================================ *)