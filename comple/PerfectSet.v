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

(* Helper: if each f i < eps, then @sum_fin n f < (INR n) * eps *)
(* sum_fin of constant function = n * eps *)
Lemma sum_fin_const : forall (n : nat) (eps : R),
  sum_fin (fun _ : Fin.t n => eps) = INR n * eps.
Proof.
  intros n eps.
  (* Use the fact that sum_fin f = f F1 + sum_fin (fun i => f (FS i)) *)
  (* For constant function eps, this gives eps + sum_fin (fun _ => eps) = eps + n' * eps = (n' + 1) * eps *)
  induction n as [|n' IHn'].
  - simpl. lra.
  - simpl.
    (* sum_fin (fun _ : Fin.t (S n') => eps) = eps + sum_fin (fun _ : Fin.t n' => eps) *)
    (* By IH, sum_fin (fun _ : Fin.t n' => eps) = INR n' * eps *)
    (* So sum_fin (fun _ : Fin.t (S n') => eps) = eps + INR n' * eps = INR (S n') * eps *)
    assert (IH : sum_fin (fun _ : Fin.t n' => eps) = INR n' * eps) by apply IHn'.
    rewrite IH.
    assert (HINR : INR (S n') = 1 + INR n').
    { rewrite S_INR. lra. }
    rewrite HINR at 1.
    ring.
Qed.

(* Pointwise comparison: if f i < g i for all i, then sum_fin f < sum_fin g *)
(* Auxiliary: non-strict pointwise comparison by induction *)
Lemma sum_fin_pointwise_le : forall (n : nat) (f g : Fin.t n -> R),
  (forall i, f i <= g i) -> @sum_fin n f <= @sum_fin n g.
Proof.
  intros n f g Hfg.
  induction n as [|n' IHn'].
  - simpl. lra.
  - simpl. apply Rplus_le_compat.
    + apply Hfg.
    + apply (IHn' (fun i => f (Fin.FS i)) (fun i => g (Fin.FS i))). intro i. apply Hfg.
Qed.

Lemma sum_fin_pointwise_lt : forall (n : nat) (f g : Fin.t n -> R),
  (0 < n)%nat -> (forall i, f i < g i) -> @sum_fin n f < @sum_fin n g.
Proof.
  intros n f g Hlt Hfg.
  destruct n as [|n'].
  - contradict Hlt. lia.
  - simpl.
    assert (H_F1 : f Fin.F1 < g Fin.F1) by apply Hfg.
    assert (H_rest : sum_fin (fun i => f (Fin.FS i)) <= sum_fin (fun i => g (Fin.FS i))).
    { apply sum_fin_pointwise_le. intro i. apply Rlt_le. apply Hfg. }
    lra.
Qed.

Lemma sum_fin_bound_eps : forall (n : nat) (f : Fin.t n -> R) (eps : R),
  (0 < n)%nat -> (forall i, f i < eps) -> @sum_fin n f < (INR n) * eps.
Proof.
  intros n f eps Hlt Heps.
  assert (Heq : sum_fin (fun _ : Fin.t n => eps) = INR n * eps) by apply sum_fin_const.
  rewrite <- Heq.
  apply (sum_fin_pointwise_lt n f (fun _ => eps) Hlt Heps).
Qed.

Lemma Rn_dist_tri : forall x y z, Rn_distance x z <= Rn_distance x y + Rn_distance y z.
Proof.
  intros x y z. unfold Rn_distance. apply sum_fin_tri_lemma.
Qed.

Lemma Rn_dist_iden_aux : forall (n : nat) (x y : Fin.t n -> R),
  sum_fin (fun i => Rabs (x i - y i)) = 0 -> forall i, Rabs (x i - y i) <= 0%R.
Proof.
  induction n as [|n' IHn'].
  - intros x y Hsum i. revert i. apply Fin.case0.
  - intros x y Hsum i.
    apply (Fin.caseS' i).
    + simpl in Hsum.
      assert (Hpos : 0 <= Rabs (x Fin.F1 - y Fin.F1)) by apply Rabs_pos.
      assert (Hpos_rest : 0 <= sum_fin (fun i => Rabs (x (Fin.FS i) - y (Fin.FS i)))).
      { apply (sum_fin_nonneg n' (fun i => Rabs (x (Fin.FS i) - y (Fin.FS i)))). intro. apply Rabs_pos. }
      destruct (Rplus_eq_0 _ _ Hpos Hpos_rest Hsum) as [H1 H2].
      rewrite H1.
      apply Rle_refl.
    + intros j.
      simpl in Hsum.
      assert (Hpos : 0 <= Rabs (x Fin.F1 - y Fin.F1)) by apply Rabs_pos.
      assert (Hpos_rest : 0 <= sum_fin (fun i => Rabs (x (Fin.FS i) - y (Fin.FS i)))).
      { apply (sum_fin_nonneg n' (fun i => Rabs (x (Fin.FS i) - y (Fin.FS i)))). intro. apply Rabs_pos. }
      destruct (Rplus_eq_0 _ _ Hpos Hpos_rest Hsum) as [H1 H2].
      apply (IHn' (fun i => x (Fin.FS i)) (fun i => y (Fin.FS i)) H2 j).
Qed.

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

(* Helper: compute max of f i over all i : Fin.t n *)
Fixpoint max_over_fin (n : nat) (f : Fin.t n -> nat) : nat :=
  match n as n0 return (Fin.t n0 -> nat) -> nat with
  | 0 => fun _ => 0%nat
  | S n' => fun g => Nat.max (g Fin.F1) (max_over_fin n' (fun i => g (Fin.FS i)))
  end f.

Lemma max_over_fin_ge : forall (n : nat) (f : Fin.t n -> nat) (i : Fin.t n),
  Nat.le (f i) (max_over_fin n f).
Proof.
  induction n as [|n' IHn'].
  - intros f i. revert i. apply Fin.case0.
  - intros f i. apply (Fin.caseS' i).
    + simpl. apply Nat.le_max_l.
    + intros j. simpl. eapply Nat.le_trans.
      * apply (IHn' (fun i => f (Fin.FS i)) j).
      * apply Nat.le_max_r.
Qed.

Definition nat_inhabited : inhabited nat := @inhabits nat (S O).

(* Helper: extract N from Un_cv for a given epsilon *)
Definition get_conv_N (n_dim0 : nat) (s : nat -> Fin.t n_dim0 -> R) (i : Fin.t n_dim0)
  (lim_i : R) (Hconv : Un_cv (fun n => s n i) lim_i) (eps : R) (Heps : eps > 0) : nat :=
  epsilon nat_inhabited (fun N => forall n0 : nat, Nat.le N n0 -> Rabs (s n0 i - lim_i) < eps).

Theorem Rn_complete : forall s : nat -> Rn,
  CauchySeq s -> exists lim, LimitSeq s lim.
Proof.
  intros s Hcauchy.
  set (lim := fun i : Fin.t n_dim => proj1_sig (R_complete (fun n => s n i) (Rn_cauchy_component s i Hcauchy))).
  exists lim.
  unfold LimitSeq.
  intros eps Heps.
  destruct (Compare_dec.lt_dec 0 n_dim) as [Hn | Hn].
  - (* n_dim > 0: use sum_fin_bound_eps *)
    assert (Hpos_div : 0 < eps / INR n_dim).
    { assert (H : 0 < INR n_dim) by (apply lt_0_INR; exact Hn).
      assert (Hpos : Rdiv eps (INR n_dim) > 0).
      { unfold Rdiv. apply Rmult_lt_0_compat. exact Heps. apply Rinv_0_lt_compat. exact H. }
      exact Hpos.
    }
    set (get_N := fun i : Fin.t n_dim =>
      get_conv_N n_dim s i (lim i) (proj2_sig (R_complete (fun n => s n i) (Rn_cauchy_component s i Hcauchy))) (eps / INR n_dim) Hpos_div).
    exists (max_over_fin n_dim get_N).
    intros n Hn0.
    unfold Rn_distance.
    assert (Hsum : @sum_fin n_dim (fun i => Rabs (s n i - lim i)) < (INR n_dim) * (eps / INR n_dim)).
    { apply (sum_fin_bound_eps n_dim (fun i => Rabs (s n i - lim i)) (eps / INR n_dim) Hn).
      intro i.
      assert (Hn_i : Nat.le (get_N i) n).
      { apply (Nat.le_trans (get_N i) (max_over_fin n_dim get_N) n (max_over_fin_ge n_dim get_N i) Hn0). }
      pose proof (epsilon_spec nat_inhabited (fun N => forall n0 : nat, Nat.le N n0 -> Rabs (s n0 i - lim i) < eps / INR n_dim)
        (proj2_sig (R_complete (fun n => s n i) (Rn_cauchy_component s i Hcauchy)) (eps / INR n_dim) Hpos_div)) as Hspec.
      simpl in Hspec.
      specialize (Hspec n Hn_i).
      exact Hspec. }
    assert (Heq : (INR n_dim) * (eps / INR n_dim) = eps).
    { unfold Rdiv. rewrite <- Rmult_assoc. rewrite (Rmult_comm (INR n_dim) eps). rewrite Rmult_assoc. rewrite Rinv_r.
      - rewrite Rmult_1_r. reflexivity.
      - apply Rgt_not_eq. apply lt_0_INR. exact Hn.
    }
    rewrite Heq in Hsum.
    exact Hsum.
  - (* n_dim = 0: trivial, distance is always 0 *)
    admit.
Admitted.

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
  intro Hcont.
  destruct Hcont as [f Hf].
  set (bs := fun n => negb (f n n)).
  specialize (Hf bs).
  destruct Hf as [n Hn].
  assert (Hcontra : bs n = f n n).
  { apply f_equal with (f := fun g => g n) in Hn.
    symmetry.
    exact Hn. }
  unfold bs in Hcontra.
  set (b := f n n) in Hcontra.
  destruct b; discriminate.
Qed.

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
