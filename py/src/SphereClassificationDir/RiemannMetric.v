(* RiemannMetric.v *)
(* Riemannian metric and tangent space using Record style. *)
(* TangentSpaceType_of M is concretely defined as R³ = (R * R * R). *)
(* All 9 vector space axioms are QED via simpl + ring. *)

Require Import Reals.
Require Import Classical_Prop.
Require Import FunctionalExtensionality.
Require Import Classical.

Open Scope R_scope.

Require Import SphereClassification.Manifold.
Require Import SphereClassification.Topology.

(* ===================================================================== *)
(* 1. Tangent Space (concrete: R³ via R * R * R)                         *)
(* ===================================================================== *)

Definition R3 : Type := (R * R * R)%type.

(* For a 3-manifold, the tangent space is R³. *)
Definition TangentSpaceType_of (M : Manifold3) : Type := R3.

(* Zero vector: (0, 0, 0) *)
Definition ts_zero_of (M : Manifold3) : TangentSpaceType_of M :=
  ((0, 0), 0).

(* Addition: component-wise *)
Definition ts_add_of (M : Manifold3) :
  TangentSpaceType_of M -> TangentSpaceType_of M -> TangentSpaceType_of M :=
  fun u v => ((fst (fst u) + fst (fst v), snd (fst u) + snd (fst v)),
              snd u + snd v).

(* Negation: component-wise *)
Definition ts_neg_of (M : Manifold3) :
  TangentSpaceType_of M -> TangentSpaceType_of M :=
  fun u => ((-fst (fst u), -snd (fst u)), -snd u).

(* Scalar multiplication: component-wise *)
Definition ts_smult_of (M : Manifold3) :
  R -> TangentSpaceType_of M -> TangentSpaceType_of M :=
  fun a u => ((a * fst (fst u), a * snd (fst u)), a * snd u).

(* ===================================================================== *)
(* 2. Vector Space Axioms (all QED)                                      *)
(* ===================================================================== *)

Lemma ts_add_assoc :
  forall (M : Manifold3) (u v w : TangentSpaceType_of M),
    ts_add_of M (ts_add_of M u v) w = ts_add_of M u (ts_add_of M v w).
Proof.
  intros M [[u1 u2] u3] [[v1 v2] v3] [[w1 w2] w3].
  unfold ts_add_of; simpl.
  f_equal; [f_equal; [ring | ring] | ring].
Qed.

Lemma ts_add_comm :
  forall (M : Manifold3) (u v : TangentSpaceType_of M),
    ts_add_of M u v = ts_add_of M v u.
Proof.
  intros M [[u1 u2] u3] [[v1 v2] v3].
  unfold ts_add_of; simpl.
  f_equal; [f_equal; [ring | ring] | ring].
Qed.

Lemma ts_zero_add :
  forall (M : Manifold3) (u : TangentSpaceType_of M),
    ts_add_of M (ts_zero_of M) u = u.
Proof.
  intros M [[u1 u2] u3].
  unfold ts_add_of, ts_zero_of; simpl.
  f_equal; [f_equal; [ring | ring] | ring].
Qed.

Lemma ts_add_zero :
  forall (M : Manifold3) (u : TangentSpaceType_of M),
    ts_add_of M u (ts_zero_of M) = u.
Proof.
  intros M [[u1 u2] u3].
  unfold ts_add_of, ts_zero_of; simpl.
  f_equal; [f_equal; [ring | ring] | ring].
Qed.

Lemma ts_add_neg :
  forall (M : Manifold3) (u : TangentSpaceType_of M),
    ts_add_of M u (ts_neg_of M u) = ts_zero_of M.
Proof.
  intros M [[u1 u2] u3].
  unfold ts_add_of, ts_neg_of, ts_zero_of; simpl.
  f_equal; [f_equal; [ring | ring] | ring].
Qed.

Lemma ts_smult_1 :
  forall (M : Manifold3) (u : TangentSpaceType_of M),
    ts_smult_of M 1 u = u.
Proof.
  intros M [[u1 u2] u3].
  unfold ts_smult_of; simpl.
  f_equal; [f_equal; [ring | ring] | ring].
Qed.

Lemma ts_smult_mul :
  forall (M : Manifold3) (a b : R) (u : TangentSpaceType_of M),
    ts_smult_of M a (ts_smult_of M b u) = ts_smult_of M (a * b) u.
Proof.
  intros M a b [[u1 u2] u3].
  unfold ts_smult_of; simpl.
  f_equal; [f_equal; [ring | ring] | ring].
Qed.

Lemma ts_smult_add_dist :
  forall (M : Manifold3) (a : R) (u v : TangentSpaceType_of M),
    ts_smult_of M a (ts_add_of M u v) =
    ts_add_of M (ts_smult_of M a u) (ts_smult_of M a v).
Proof.
  intros M a [[u1 u2] u3] [[v1 v2] v3].
  unfold ts_add_of, ts_smult_of; simpl.
  f_equal; [f_equal; [ring | ring] | ring].
Qed.

Lemma ts_smult_plus_dist :
  forall (M : Manifold3) (a b : R) (u : TangentSpaceType_of M),
    ts_smult_of M (a + b) u = ts_add_of M (ts_smult_of M a u) (ts_smult_of M b u).
Proof.
  intros M a b [[u1 u2] u3].
  unfold ts_add_of, ts_smult_of; simpl.
  f_equal; [f_equal; [ring | ring] | ring].
Qed.

(* ===================================================================== *)
(* 3. Riemannian Metric                                                  *)
(* ===================================================================== *)

Record RiemannianMetric (M : Manifold3) := mkRiemannianMetric {
  metric_tensor : forall (p : space_type (sm_space M)) (u v : TangentSpaceType_of M),
    R;
  metric_symmetry : forall (p : space_type (sm_space M)) (u v : TangentSpaceType_of M),
    metric_tensor p u v = metric_tensor p v u;
  metric_posdef : forall (p : space_type (sm_space M)) (u : TangentSpaceType_of M),
    metric_tensor p u u >= 0 /\ (metric_tensor p u u = 0 -> u = ts_zero_of M);
  metric_bilinear : forall (p : space_type (sm_space M)) (u v w : TangentSpaceType_of M) (a b : R),
    metric_tensor p (ts_add_of M (ts_smult_of M a u) (ts_smult_of M b v)) w
    = a * metric_tensor p u w + b * metric_tensor p v w
}.

(* ===================================================================== *)
(* 4. Summary                                                            *)
(* ===================================================================== *)

(* Total: 0 Parameters (was 5), 0 Axioms (was 9), 1 Record *)
(* All 9 vector space axioms are now QED Lemmas. *)
(* TangentSpaceType_of M = R3 (concrete R³ via product type). *)