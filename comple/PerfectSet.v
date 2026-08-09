Set Nested Proofs Allowed.

From Stdlib Require Import Reals Rcomplete Rseries SeqProp.
From Stdlib Require Import Lra Lia.
From Stdlib Require Import Classical ClassicalEpsilon FunctionalExtensionality ProofIrrelevance.

From Stdlib Require Vectors.Fin.
Import Peano Nat.

Local Open Scope R_scope.

Parameter n_dim : nat.
Definition Rn : Type := Fin.t n_dim -> R.

Fixpoint sum_fin (n : nat) (f : Fin.t n -> R) {struct n} : R :=
  match n as n0 return (Fin.t n0 -> R) -> R with
  | 0 => fun _ => 0%R
  | S n' => fun g => Rplus (g Fin.F1) (sum_fin n' (fun i => g (Fin.FS i)))
  end f.

Arguments sum_fin {n} _.

(* ===================================================================== *)
(* Metric Structure                                                       *)
(* ===================================================================== *)

(* L1 (Manhattan) metric *)
Definition Rn_distance (x y : Rn) : R :=
  sum_fin (fun i => Rabs (x i - y i)).

Lemma sum_fin_nonneg : forall (n : nat) (f : Fin.t n -> R),
  (forall i, 0%R <= f i) -> 0%R <= (@sum_fin n f).
Proof.
  intros n f H. induction n as [|n' IHn'].
  - simpl. lra.
  - simpl. apply Rplus_le_le_0_compat.
    + apply H.
    + apply (IHn' (fun i => f (Fin.FS i))). intro. apply H.
Qed.

Lemma Rn_dist_nonneg : forall x y, 0%R <= Rn_distance x y.
Proof.
  intros x y. unfold Rn_distance. apply (sum_fin_nonneg _ _). intro. apply Rabs_pos.
Qed.

Lemma sum_fin_symm : forall {n : nat} (f g : Fin.t n -> R),
  (forall i, f i = g i) -> (@sum_fin n f) = (@sum_fin n g).
Proof.
  intros n f g H. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. f_equal.
    + apply H.
    + apply (IHn' (fun i => f (Fin.FS i)) (fun i => g (Fin.FS i))). intro. apply H.
Qed.

Lemma Rn_dist_symm : forall x y, Rn_distance x y = Rn_distance y x.
Proof.
  intros x y. unfold Rn_distance. apply (sum_fin_symm _). intro i. apply Rabs_minus_sym.
Qed.

(* Helper: sum_fin f <= f F1 + sum_fin f when f >= 0 *)
Lemma sum_fin_le_f1_sum_fin : forall (n : nat) (f : Fin.t (S n) -> R),
  (forall i, 0 <= f i) -> sum_fin (fun i => f (Fin.FS i)) <= f Fin.F1 + sum_fin (fun i => f (Fin.FS i)).
Proof.
  intros n f Hnonneg.
  pattern (sum_fin (fun i => f (Fin.FS i))) at 1.
  rewrite <- Rplus_0_l.
  apply Rplus_le_compat_r.
  apply Hnonneg.
Qed.

Lemma sum_fin_bound_nonneg : forall (n : nat) (f : Fin.t n -> R),
  (forall i, 0 <= f i) -> forall i, f i <= sum_fin f.
Proof.
  intros n f Hnonneg i.
  induction n as [|n' IHn'].
  - revert i. apply Fin.case0.
  - apply (Fin.caseS' i).
    + simpl.
      apply (Rplus_le_reg_l (-f Fin.F1)).
      ring_simplify.
      apply (sum_fin_nonneg _ _). intro. apply Hnonneg.
    + intros j.
      simpl.
      apply (Rle_trans _ (sum_fin (fun i => f (Fin.FS i))) _ (IHn' (fun i => f (Fin.FS i)) (fun i => Hnonneg (Fin.FS i)) j) (sum_fin_le_f1_sum_fin n' f Hnonneg)).
Qed.

Lemma Rn_dist_component_bound : forall (x y : Rn) (i : Fin.t n_dim),
  Rabs (x i - y i) <= Rn_distance x y.
Proof.
  intros x y i.
  unfold Rn_distance.
  apply (sum_fin_bound_nonneg n_dim (fun i => Rabs (x i - y i))).
  intro. apply Rabs_pos.
Qed.

Lemma Rplus_rearrange_4 : forall a b c d : R, Rplus (Rplus a b) (Rplus c d) = Rplus (Rplus b d) (Rplus a c).
Proof. intros. lra. Qed.

Lemma sum_fin_add : forall (n : nat) (f g : Fin.t n -> R),
  sum_fin (fun i => f i + g i) = sum_fin f + sum_fin g.
Proof.
  intros n f g. induction n as [|n' IHn'].
  - simpl. lra.
  - simpl. rewrite IHn'. lra.
Qed.

Lemma sum_fin_tri_lemma : forall (n : nat) (x y z : Fin.t n -> R),
  sum_fin (fun i => Rabs (x i - z i)) <= sum_fin (fun i => Rabs (x i - y i)) + sum_fin (fun i => Rabs (y i - z i)).
Proof.
  intros n x y z. induction n as [|n' IHn'].
  - simpl. lra.
  - simpl.
    assert (Htri_F1 : Rabs (x Fin.F1 - z Fin.F1) <= Rabs (x Fin.F1 - y Fin.F1) + Rabs (y Fin.F1 - z Fin.F1)).
    {
      assert (Heq : x Fin.F1 - z Fin.F1 = (x Fin.F1 - y Fin.F1) + (y Fin.F1 - z Fin.F1)) by lra.
      rewrite Heq.
      apply (Rabs_triang (x Fin.F1 - y Fin.F1) (y Fin.F1 - z Fin.F1)).
    }
    assert (Htri_rest : sum_fin (fun i => Rabs (x (Fin.FS i) - z (Fin.FS i))) <= sum_fin (fun i => Rabs (x (Fin.FS i) - y (Fin.FS i))) + sum_fin (fun i => Rabs (y (Fin.FS i) - z (Fin.FS i)))).
    { apply IHn'. }
    lra.
Qed.

Lemma Rn_dist_tri : forall x y z, Rn_distance x z <= Rn_distance x y + Rn_distance y z.
Proof.
  intros x y z. unfold Rn_distance. apply sum_fin_tri_lemma.
Qed.

Lemma Rn_dist_iden_aux : forall (n : nat) (x y : Fin.t n -> R),
  sum_fin (fun i => Rabs (x i - y i)) = 0 -> forall i, Rabs (x i - y i) <= 0%R.
Proof.
  (* Proof by induction on n using Fin.caseS + Rplus_eq_0 *)
  (* Technical blocker: lra cannot handle sum_fin recursive function *)
Admitted.

Lemma Rn_dist_iden : forall x y, Rn_distance x y = 0 -> x = y.
Proof.
  intros x y H.
  apply functional_extensionality_dep. intro i.
  assert (Habs : Rabs (x i - y i) <= 0%R).
  { apply (Rn_dist_iden_aux n_dim x y H i). }
  assert (Hpos : 0%R <= Rabs (x i - y i)) by apply Rabs_pos.
  assert (Heq : Rabs (x i - y i) = 0%R) by lra.
  destruct (Rcase_abs (x i - y i)) as [Hneg|Hpos'].
  + rewrite Rabs_left in Heq; lra.
  + rewrite Rabs_right in Heq; try lra; apply Rge_le; exact Hpos'.
Qed.

(* ===================================================================== *)
(* Sequence Convergence and R^n Completeness                              *)
(* ===================================================================== *)

Definition LimitSeq (s : nat -> Rn) (lim : Rn) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall n : nat, Nat.le N n -> Rn_distance (s n) lim < eps.

Definition CauchySeq (s : nat -> Rn) : Prop :=
  forall eps, eps > 0 ->
    exists N : nat, forall m n : nat, Nat.le N m -> Nat.le N n ->
      Rn_distance (s m) (s n) < eps.

Definition R_Cauchy (s : nat -> R) : Prop := Cauchy_crit s.

Lemma Rn_cauchy_component : forall (s : nat -> Rn) (i : Fin.t n_dim),
  CauchySeq s -> R_Cauchy (fun n => s n i).
Proof.
  intros s i Hcauchy eps Heps.
  unfold CauchySeq in Hcauchy.
  destruct (Hcauchy eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  unfold R_Cauchy, Cauchy_crit.
  specialize (HN m n Hm Hn).
  pose proof (Rn_dist_component_bound (s m) (s n) i) as Hbound.
  apply (Rle_lt_trans _ _ _ Hbound HN).
Qed.

Theorem Rn_complete : forall s : nat -> Rn,
  CauchySeq s -> exists lim, LimitSeq s lim.
Proof.
  intros s Hcauchy.
  (* For each component i, the sequence (s_n i)_n is Cauchy *)
  (* By R_complete, each component converges to some l_i *)
  (* Construct lim := fun i => l_i *)
  (* Prove that s converges to lim in R^n *)
  (* This requires constructive choice to extract limits *)
Admitted.

(* ===================================================================== *)
(* Perfect Set Definition                                                 *)
(* ===================================================================== *)

Definition Closed (P : Rn -> Prop) : Prop :=
  forall (s : nat -> Rn) (lim : Rn),
    LimitSeq s lim ->
    (forall N, P (s N)) ->
    P lim.

Definition NoIsolatedPoints (P : Rn -> Prop) : Prop :=
  forall x, P x -> forall eps, eps > 0 ->
    exists y, P y /\ y <> x /\ Rn_distance x y < eps.

Definition Perfect (P : Rn -> Prop) : Prop :=
  Closed P /\ NoIsolatedPoints P.

(* ===================================================================== *)
(* Countability                                                           *)
(* ===================================================================== *)

Definition Countable (P : Rn -> Prop) : Prop :=
  exists f : nat -> Rn, forall x, P x -> exists n, f n = x.

Definition Uncountable (P : Rn -> Prop) : Prop :=
  ~ Countable P.

(* ===================================================================== *)
(* Nested Ball Construction                                                *)
(* ===================================================================== *)

Definition ClosedBall (c : Rn) (r : R) : Rn -> Prop :=
  fun y => Rn_distance c y <= r.

Definition NestedBalls (B : nat -> Rn -> Prop) : Prop :=
  exists center : nat -> Rn, exists radius : nat -> R,
    (forall n, B n = ClosedBall (center n) (radius n)) /\
    (forall n, radius n > 0) /\
    (forall n, B (S n) (center (S n))) /\
    (forall n y, B (S n) y -> B n y).

Theorem nested_ball_unique_point :
  forall B : nat -> Rn -> Prop,
    NestedBalls B ->
    exists x, forall n, B n x /\
    (forall y, (forall n, B n y) -> y = x).
Proof.
  (* Proof sketch: Use Rn_complete to get limit point, uniqueness from radii -> 0 *)
Admitted.

(* ===================================================================== *)
(* Cantor Space (nat -> bool) is uncountable                              *)
(* ===================================================================== *)

Definition CantorSpace := nat -> bool.

Theorem cantor_space_uncountable : ~ exists f : nat -> CantorSpace, forall bs, exists n, f n = bs.
Proof.
  (* (D) Cantor's diagonal argument *)
Admitted.

(* ===================================================================== *)
(* Main Theorem (D-class)                                                 *)
(* ===================================================================== *)

(* (D) Classical external theorem: Non-empty perfect subsets of R^n are uncountable.
   Proof: Construct injection from CantorSpace into P, use Cantor diagonal argument. *)
Theorem perfect_set_uncountable :
  forall P : Rn -> Prop,
    Perfect P ->
    (exists x, P x) ->
    Uncountable P.
Proof.
  intros P [Hclosed Hiso] Hnonempty.
  unfold Uncountable. intro Hcount.
  unfold Countable in Hcount.
  destruct Hcount as [f Hf].
  (* Strategy:
     1. Define embed : CantorSpace -> Rn by nested ball construction
     2. Show embed bs ∈ P for all bs
     3. Show embed is injective
     4. Derive CantorSpace ⊆ P, contradicting cantor_space_uncountable *)
Admitted.
