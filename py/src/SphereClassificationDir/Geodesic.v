(* Geodesic.v *)
(* Geodesics and exponential map using Record style. *)

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
(* 1. Geodesic                                                           *)
(* ===================================================================== *)

Record Geodesic (M : Manifold3) (g : RiemannianMetric M) := mkGeodesic {
  (* Geodesic as a curve *)
  geodesic_path : R -> TangentSpaceType_of M;
  (* Geodesic equation: ∇_{γ'} γ' = 0 (abstracted) *)
  geodesic_eq : True;
  (* Initial conditions *)
  geodesic_start : TangentSpaceType_of M;
  geodesic_velocity : TangentSpaceType_of M;
  geodesic_initial : geodesic_path 0 = geodesic_start
}.

(* ===================================================================== *)
(* 2. Exponential Map                                                    *)
(* ===================================================================== *)

Record ExponentialMap (M : Manifold3) (g : RiemannianMetric M) := mkExponentialMap {
  exp_map : TangentSpaceType_of M -> space_type (sm_space M);
  (* exp_p(0) = p *)
  exp_zero : forall p, exp_map (ts_zero_of M) = p;
  (* exp_p(tv) = γ_v(t) (abstracted) *)
  exp_geodesic : True;
  (* d(exp_p)_0 = id (abstracted) *)
  exp_differential : True
}.

(* ===================================================================== *)
(* 3. Geodesic Completeness                                              *)
(* ===================================================================== *)

Record IsGeodesicallyComplete (M : Manifold3) (g : RiemannianMetric M) := mkIsGeodesicallyComplete {
  geodesic_complete : Prop
}.

(* ===================================================================== *)
(* 4. Summary                                                            *)
(* ===================================================================== *)

(* Total: 3 Records *)
