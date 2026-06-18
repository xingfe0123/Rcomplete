(* ArzelaAscoli.v *)
(* Arzelà-Ascoli Theorem: equicontinuous + uniformly bounded *)
(* family of continuous functions on a compact set is relatively compact. *)
(* Reference: Arzelà 1882, Ascoli 1883, Rudin 1976.           *)

Require Import Reals.
Require Import Classical_Prop.
Require Import Ensembles.
Require Import Reals Lra.
Require Import FunctionalExtensionality.
Require Import Classical.

Open Scope R_scope.
Open Scope nat_scope.

Require Import CompactEmbedding.MetricCompact.

(* ===================================================================== *)
(* 1. Uniformly Bounded Family                                            *)
(* ===================================================================== *)

(* A family F ⊆ C(K) is uniformly bounded if ∃M, ∀f ∈ F, ∀x ∈ K, |f(x)| ≤ M *)
Definition UniformlyBounded (K : Rn -> Prop) (F : C0_on K -> Prop) : Prop :=
  exists M : R, M > 0 /\
    forall (f : C0_on K),
      F f ->
      forall (x : Rn),
        K x ->
        Rabs (func_of_C0 f x) <= M.

(* ===================================================================== *)
(* 2. Equicontinuous Family                                               *)
(* ===================================================================== *)

(* A family F ⊆ C(K) is equicontinuous if *)
(* ∀ε > 0, ∃δ > 0, ∀f ∈ F, ∀x, y ∈ K, d(x,y) < δ ⇒ |f(x) - f(y)| < ε *)
Definition Equicontinuous (K : Rn -> Prop) (F : C0_on K -> Prop) : Prop :=
  forall eps : R, eps > 0 ->
    exists delta : R, delta > 0 /\
      forall (f : C0_on K),
        F f ->
        forall (x y : Rn),
          K x -> K y -> Rn_distance x y < delta ->
          Rabs (func_of_C0 f x - func_of_C0 f y) < eps.

(* ===================================================================== *)
(* 3. Relatively Compact (closure is compact)                             *)
(* ===================================================================== *)

(* A subset F of C(K) is relatively compact if its closure is compact *)
(* In metric spaces, this is equivalent to: every sequence in F has *)
(* a convergent subsequence (in the uniform metric). *)
Definition RelativelyCompact (K : Rn -> Prop) (F : C0_on K -> Prop) : Prop :=
  True.  (* Abstracted - requires uniform metric on C(K) *)

(* ===================================================================== *)
(* 4. Arzelà-Ascoli Theorem (Axiom)                                       *)
(* ===================================================================== *)

(* Main theorem: equicontinuous + uniformly bounded => relatively compact *)
Axiom arzela_ascoli :
  forall (K : Rn -> Prop) (F : C0_on K -> Prop),
    is_compact K ->
    Equicontinuous K F ->
    UniformlyBounded K F ->
    RelativelyCompact K F.

(* ===================================================================== *)
(* 5. Corollary: Sequence Version                                         *)
(* ===================================================================== *)

(* Every sequence of equicontinuous + uniformly bounded functions *)
(* has a uniformly convergent subsequence *)
Axiom arzela_ascoli_sequence :
  forall (K : Rn -> Prop) (seq : nat -> C0_on K),
    is_compact K ->
    (forall n : nat, True) ->  (* Each f_n is in the family (trivial) *)
    (forall eps : R, eps > 0 -> exists delta : R, delta > 0 /\
      forall (n : nat) (x y : Rn), K x -> K y -> Rn_distance x y < delta ->
        Rabs (func_of_C0 (seq n) x - func_of_C0 (seq n) y) < eps) ->  (* equicontinuous *)
    (exists M : R, M > 0 /\
      forall (n : nat) (x : Rn), K x -> Rabs (func_of_C0 (seq n) x) <= M) ->  (* uniformly bounded *)
    True.  (* There exists a convergent subsequence - abstracted *)

(* ===================================================================== *)
(* 6. Summary                                                            *)
(* ===================================================================== *)

(* Total Definitions: 3 *)
(*   UniformlyBounded *)
(*   Equicontinuous *)
(*   RelativelyCompact *)
(* Total Axioms: 2 *)
(*   arzela_ascoli : main theorem (family version) *)
(*   arzela_ascoli_sequence : corollary (sequence version) *)
(* Total Theorems: 0 (main statements are Axioms) *)
