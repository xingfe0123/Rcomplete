From Stdlib Require Import Reals RIneq Ranalysis.
From Stdlib Require Import Lra.
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

Lemma Rmult_le_compat_r_pos : forall r r1 r2 : R, r > 0 -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros r r1 r2 Hpos Hle.
  apply Rmult_le_compat_l.
  lra.
  exact Hle.
Qed.

Lemma dist_nonneg :
  forall (ms : MetricSpace) (x y : ms),
    0 <= @dist ms x y.

Proof.
  intros ms x y.
  assert (H1 : @dist ms x x <= @dist ms x y + @dist ms y x).
  { apply (@dist_triangle ms). }
  rewrite (@dist_self ms) in H1.
  assert (H2 : @dist ms x y + @dist ms y x = @dist ms x y + @dist ms x y).
  { f_equal. apply (@dist_sym ms). }
  rewrite H2 in H1.
  assert (H3 : @dist ms x y + @dist ms x y = 2 * @dist ms x y).
  { lra. }
  rewrite H3 in H1.
  assert (H4 : / 2 > 0).
  { apply Rinv_0_lt_compat. lra. }
  assert (H5 := Rmult_le_compat_r_pos (/ 2) 0 (2 * @dist ms x y) H4 H1).
  assert (H6a : / 2 * 2 = 1).
  { rewrite Rmult_comm. apply Rinv_r. lra. }
  assert (H6 : / 2 * (2 * @dist ms x y) = @dist ms x y).
  { rewrite <- Rmult_assoc. rewrite H6a. rewrite Rmult_1_l. lra. }
  assert (H7 : / 2 * 0 = 0).
  { apply Rmult_0_r. }
  rewrite H6 in H5. rewrite H7 in H5.
  exact H5.
Qed.

(******************************************************************************)
(* 序列收敛定义                                                                *)
(******************************************************************************)

Definition convergent (ms : MetricSpace) (p : nat -> ms) (p0 : ms) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall n : nat, (N <= n)%nat -> @dist ms (p n) p0 < eps.

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
  assert (Hinv : / 2 > 0).
  { apply Rinv_0_lt_compat. lra. }
  assert (Hres := Rmult_lt_compat_l (/ 2) 0 eps Hinv Heps).
  rewrite Rmult_0_r in Hres.
  lra.
Qed.

(******************************************************************************)
(* 定理：极限的唯一性                                                          *)
(******************************************************************************)

Theorem limit_unique :
  forall (ms : MetricSpace) (p : nat -> ms) (p1 p2 : ms),
    convergent ms p p1 -> convergent ms p p2 -> p1 = p2.

Proof.
  intros ms p p1 p2 H1 H2.
  apply (@dist_eq_ident ms).
  assert (Hge : 0 <= @dist ms p1 p2).
  { apply dist_nonneg. }
  assert (Hle : @dist ms p1 p2 <= 0).
  { apply lt_all_eps_le_0.
    intros eps Heps.
    pose proof (half_gt_zero eps Heps) as Hhalf.
    specialize (H1 (eps / 2) Hhalf) as [N1 HN1].
    specialize (H2 (eps / 2) Hhalf) as [N2 HN2].
    pose proof (@dist_triangle ms p1 (p (N1 + N2)%nat) p2) as Htri.
    rewrite (@dist_sym ms p1 (p (N1 + N2)%nat)) in Htri.
    pose proof (HN1 (N1 + N2)%nat) as H1b.
    pose proof (HN2 (N1 + N2)%nat) as H2b.
    assert (H1bound : @dist ms (p (N1 + N2)%nat) p1 < eps / 2).
    { apply H1b. lia. }
    assert (H2bound : @dist ms (p (N1 + N2)%nat) p2 < eps / 2).
    { apply H2b. lia. }
    assert (Hsum : @dist ms (p (N1 + N2)%nat) p1 + @dist ms (p (N1 + N2)%nat) p2 < eps).
    { lra. }
    assert (Hfin : @dist ms p1 p2 < eps).
    { eapply Rle_lt_trans. exact Htri. exact Hsum. }
    exact Hfin. }
  apply Rle_antisym.
  exact Hle.
  exact Hge.
Qed.
