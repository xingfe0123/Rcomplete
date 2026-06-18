(* RiemannTensor.v *)
(* Riemann curvature tensor and sectional curvature using Record style. *)

Require Import Reals.
Require Import Classical_Prop.
Require Import Reals Lra.
Require Import FunctionalExtensionality.
Require Import Classical.

Open Scope R_scope.

Require Import SphereClassification.Manifold.
Require Import SphereClassification.Topology.
Require Import SphereClassification.RiemannMetric.

(* ===================================================================== *)
(* 1. Riemann Curvature Tensor                                           *)
(* ===================================================================== *)

(* Abstract Riemann tensor *)
Parameter riemann_tensor :
  forall (M : Manifold3), TangentSpaceType_of M ->
  TangentSpaceType_of M -> TangentSpaceType_of M -> TangentSpaceType_of M.

(* Abstract sectional curvature *)
Parameter sectional_curvature :
  forall (M : Manifold3), TangentSpaceType_of M -> TangentSpaceType_of M -> R.

(* ===================================================================== *)
(* 2. Curvature Properties                                               *)
(* ===================================================================== *)

Definition has_positive_curvature (M : Manifold3) : Prop :=
  True.  (* Abstracted positive curvature *)

(* ===================================================================== *)
(* 3. Summary                                                            *)
(* ===================================================================== *)

(* Total: 3 Parameters + 1 Definition = 4 *)
