(* ============================================================================ *)
(*  CommonDefs.v                                                                *)
(*  定理文件公共辅助定义                                                         *)
(*                                                                            *)
(*  提供基于 IncidenceStructure 的通用几何概念:                                  *)
(*    Collinear, LinesIntersect, IntersectionPoint                              *)
(*                                                                            *)
(*  使用者: DesarguesTheorem.v, EuclideanTheorem.v, PascalTheorem.v              *)
(* ============================================================================ *)

From Hilbert Require Import HilbertStructure.

Section CommonDefs.

  Variable (I : IncidenceStructure).

  (* 三点共线: 存在一条直线同时经过三点 *)
  Definition Collinear (A B C : IncPoint I) : Prop :=
    exists l : IncLine I, Incid I A l /\ Incid I B l /\ Incid I C l.

  (* 两直线相交: 存在唯一的交点 *)
  Definition LinesIntersect (a b : IncLine I) : Prop :=
    exists! P : IncPoint I, Incid I P a /\ Incid I P b.

  (* 两条线交于一点 *)
  Definition IntersectionPoint (a b : IncLine I) (P : IncPoint I) : Prop :=
    Incid I P a /\ Incid I P b.

End CommonDefs.
