(* ============================================================================ *)
(*  Common.v                                                                   *)
(*  Tier-2 共享基础层: Hilbert 公理系统的所有基本对象与基本关系                  *)
(*                                                                            *)
(*  本文件只引入 Parameter, 不引入任何 Axiom                                    *)
(*  所有 Axiom 在 IncidenceAxioms.v / OrderAxioms.v / CongruenceAxioms.v /     *)
(*  ParallelAxioms.v / ContinuityAxioms.v 中各自声明                            *)
(*                                                                            *)
(*  对象 / 关系分类:                                                           *)
(*    - 点 / 直线 / 平面:  三类几何对象                                         *)
(*    - Incid:            关联 (点在直线上)                                     *)
(*    - Bet:              顺序 (点在两点之间)                                   *)
(*    - Parallel:         平行 (两直线)                                        *)
(*    - SameSide:         同侧 (在直线上)                                       *)
(*    - SameSideAngle:    同侧 (在角内, 用于 Pasch 变体)                        *)
(*                                                                            *)
(*  Cong / Segment / Angle 在 CongruenceAxioms.v 中独立声明                     *)
(* ============================================================================ *)

From Stdlib Require Import Classical.

(* ============================================================================ *)
(*  基本对象                                                                   *)
(* ============================================================================ *)

Parameter Point : Type.
Parameter Line  : Type.
Parameter Plane : Type.

(* ============================================================================ *)
(*  关联关系 (Incid: 点在直线上 / 点在平面上)                                    *)
(* ============================================================================ *)

Parameter Incid        : Point -> Line  -> Prop.  (* P ∈ l   点 P 在直线 l  *)
Parameter IncidPlane   : Point -> Plane -> Prop.  (* P ∈ α   点 P 在平面 α  *)

(* ============================================================================ *)
(*  顺序关系 (Bet: B 在 A, C 之间)                                              *)
(* ============================================================================ *)

Parameter Bet : Point -> Point -> Point -> Prop.

(* ============================================================================ *)
(*  平行关系 (Parallel: 两直线平行)                                              *)
(* ============================================================================ *)

Parameter Parallel : Line -> Line -> Prop.

(* ============================================================================ *)
(*  同侧关系 (Tier-2 完整化: Hilbert 需要"在直线一侧"来表述角)                   *)
(*                                                                            *)
(*  SameSide a P Q       : P, Q 在直线 a 的同侧 (即 a 不穿过 PQ 线段)           *)
(*  SameSideAngle h k P  : P 在角 ∠(h,k) 的内部                                 *)
(*                                                                            *)
(*  这两个谓词用于 Pasch 公理的等价表述与角的严格定义                            *)
(* ============================================================================ *)

Parameter SameSide      : Line  -> Point -> Point -> Prop.
Parameter SameSideAngle : Line  -> Line  -> Point -> Prop.

(* ============================================================================ *)
(*  派生记号: 反射 / 对称 / 反自反                                                *)
(* ============================================================================ *)

Definition distinct (A B : Point) : Prop := A <> B.
Definition on_line (P : Point) (l : Line) : Prop := Incid P l.
Definition on_plane (P : Point) (alpha : Plane) : Prop := IncidPlane P alpha.

(* 平行公理常用形式: 三元组 (P,a) 上"过 P 与 a 平行的唯一直线"                    *)
(* 定义为 Predicate, 实际使用 Axiom IV_1 量化                                  *)
Definition ParallelThrough (P : Point) (a : Line) (b : Line) : Prop :=
  Incid P b /\ Parallel a b.