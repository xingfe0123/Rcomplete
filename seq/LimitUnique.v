From Stdlib Require Import Reals RIneq Ranalysis.
From Stdlib Require Import Lia.

Open Scope R_scope.

(******************************************************************************)
(* 度量空间定义                                                                *)
(******************************************************************************)

Record MetricSpace : Type := {
  Carrier :> Type;
  dist : Carrier -> Carrier -> R;
  dist_self : forall x, dist x x = 0;
  dist_sym : forall x y, dist x y = dist y x;
  dist_triangle : forall x y z, dist x z <= dist x y + dist y z;
  dist_eq_ident : forall x y, dist x y = 0 -> x = y
}.

(******************************************************************************)
(* 距离非负性（可从公理推导）                                                   *)
(******************************************************************************)

Lemma dist_nonneg :
  forall (ms : MetricSpace) (x y : ms),
    0 <= dist x y.

Proof.
  intros ms x y.
  pose proof (@dist_triangle ms) as Htri.
  pose proof (@dist_self ms) as Hself.
  pose proof (@dist_sym ms) as Hsym.
  assert (H : dist x x <= dist x y + dist y x).
  { apply Htri. }
  rewrite Hself in H.
  rewrite (Hsym x y) in H.
  lra.
Qed.

(******************************************************************************)
(* 序列收敛定义                                                                *)
(******************************************************************************)

Definition convergent (ms : MetricSpace) (p : nat -> ms) (p0 : ms) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall n : nat, (N <= n)%nat -> dist (p n) p0 < eps.

(******************************************************************************)
(* 引理：若 x < eps 对所有 eps > 0 成立，则 x <= 0                              *)
(******************************************************************************)

Lemma lt_all_eps_le_0 (x : R) :
  (forall eps : R, eps > 0 -> x < eps) -> x <= 0.
Proof.
  intros H.
  apply Rnot_lt_le.
  intro Hpos.
  specialize (H x Hpos).
  lra.
Qed.

(******************************************************************************)
(* 引理：eps / 2 > 0 当 eps > 0                                               *)
(******************************************************************************)

Lemma half_gt_zero (eps : R) :
  eps > 0 -> eps / 2 > 0.
Proof.
  intro Heps.
  unfold Rdiv.
  apply Rmult_lt_compat_l.
  - apply Rinv_0_lt_compat. lra.
  - apply Heps.
Qed.

(******************************************************************************)
(* 定理：极限的唯一性                                                          *)
(******************************************************************************)

Theorem limit_unique :
  forall (ms : MetricSpace) (p : nat -> ms) (p1 p2 : ms),
    convergent p p1 -> convergent p p2 -> p1 = p2.

Proof.
  intros ms p p1 p2 H1 H2.
  apply (dist_eq_ident ms).
  apply Rle_antisym.
  - apply dist_nonneg.
  - apply lt_all_eps_le_0.
    intros eps Heps.
    pose proof (half_gt_zero eps Heps) as Hhalf.
    specialize (H1 (eps / 2) Hhalf) as [N1 HN1].
    specialize (H2 (eps / 2) Hhalf) as [N2 HN2].
    assert (Hlt : dist p1 p2 <= dist p1 (p (N1 + N2)) + dist (p (N1 + N2)) p2).
    { rewrite (dist_sym p1 (p (N1 + N2))).
      apply dist_triangle. }
    assert (H1bound : dist p1 (p (N1 + N2)) < eps / 2).
    { apply HN1. lia. }
    assert (H2bound : dist (p (N1 + N2)) p2 < eps / 2).
    { apply HN2. lia. }
    lra.
Qed.
