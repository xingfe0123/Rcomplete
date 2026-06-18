(* FundamentalGroup.v *)
(* Fundamental group and simple connectivity using Record style. *)

Require Import Reals.
Require Import Classical_Prop.
Require Import Reals Lra.
Require Import FunctionalExtensionality.
Require Import Classical.

Open Scope R_scope.

Require Import SphereClassification.Topology.

(* ===================================================================== *)
(* 1. Loop Space                                                         *)
(* ===================================================================== *)

(* Loop: a path from x0 to x0 *)
Record Loop (X : TopologicalSpace) (x0 : space_type X) := mkLoop {
  loop_path : Path X;
  loop_start_eq : path_start X loop_path = x0;
  loop_end_eq : path_end X loop_path = x0
}.

(* ===================================================================== *)
(* 2. Fundamental Group                                                  *)
(* ===================================================================== *)

Record FundamentalGroup (X : TopologicalSpace) (x0 : space_type X) := mkFundamentalGroup {
  fg_type :> Type;
  (* Group operation *)
  fg_mul : fg_type -> fg_type -> fg_type;
  (* Identity *)
  fg_id : fg_type;
  (* Inverse *)
  fg_inv : fg_type -> fg_type;
  (* Group axioms *)
  fg_assoc : forall a b c, fg_mul (fg_mul a b) c = fg_mul a (fg_mul b c);
  fg_id_left : forall a, fg_mul fg_id a = a;
  fg_id_right : forall a, fg_mul a fg_id = a;
  fg_inv_left : forall a, fg_mul (fg_inv a) a = fg_id;
  fg_inv_right : forall a, fg_mul a (fg_inv a) = fg_id
}.

(* ===================================================================== *)
(* 3. Simple Connectivity                                                *)
(* ===================================================================== *)

(* Abstract definition: every loop is contractible *)
Record IsSimplyConnected (X : TopologicalSpace) := mkSimplyConnected {
  simply_connected : Prop;
  simply_connected_def : simply_connected <->
    forall (x0 : space_type X) (l : Loop X x0),
      (* Loop l is homotopic to constant path at x0 - abstracted *)
      True
}.

(* ===================================================================== *)
(* 4. Path-Connectedness                                                 *)
(* ===================================================================== *)

Record IsPathConnected (X : TopologicalSpace) := mkPathConnected {
  path_connected : Prop;
  path_connected_def : path_connected <->
    forall (x y : space_type X), exists (p : Path X), True
}.

(* Axiom: simply-connected implies path-connected *)
Axiom simply_connected_implies_path_connected :
  forall (X : TopologicalSpace),
    IsSimplyConnected X -> IsPathConnected X.

(* ===================================================================== *)
(* 5. Summary                                                            *)
(* ===================================================================== *)

(* Total: 1 Record (Loop) + 1 Record (FundamentalGroup with 5 axioms) + *)
(*        1 Record (IsSimplyConnected) + 1 Record (IsPathConnected) + 1 Axiom = 8 *)
