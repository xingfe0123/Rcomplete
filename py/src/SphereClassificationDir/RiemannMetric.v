(* RiemannMetric.v *)
(* Riemannian metric and tangent space using Record style. *)
(* Minimal version to ensure compilation. *)

Require Import Reals.
Require Import Classical_Prop.
Require Import Reals Lra.
Require Import FunctionalExtensionality.
Require Import Classical.

Open Scope R_scope.

Require Import SphereClassification.Manifold.
Require Import SphereClassification.Topology.

(* ===================================================================== *)
(* 1. Tangent Space (abstract)                                           *)
(* ===================================================================== *)

Parameter TangentSpaceType_of : Manifold3 -> Type.
Parameter ts_zero_of : forall (M : Manifold3), TangentSpaceType_of M.
Parameter ts_add_of : forall (M : Manifold3),
  TangentSpaceType_of M -> TangentSpaceType_of M -> TangentSpaceType_of M.
Parameter ts_smult_of : forall (M : Manifold3),
  R -> TangentSpaceType_of M -> TangentSpaceType_of M.

(* ===================================================================== *)
(* 2. Riemannian Metric                                                  *)
(* ===================================================================== *)

Record RiemannianMetric (M : Manifold3) := mkRiemannianMetric {
  metric_tensor : forall (p : space_type (sm_space M)) (u v : TangentSpaceType_of M),
    R;
  metric_symmetry : forall (p : space_type (sm_space M)) (u v : TangentSpaceType_of M),
    metric_tensor p u v = metric_tensor p v u;
  metric_posdef : forall (p : space_type (sm_space M)) (u : TangentSpaceType_of M),
    metric_tensor p u u >= 0 /\ (metric_tensor p u u = 0 -> u = ts_zero_of M)
}.

(* ===================================================================== *)
(* 3. Summary                                                            *)
(* ===================================================================== *)

(* Total: 4 Parameters + 1 Record = 5 *)
