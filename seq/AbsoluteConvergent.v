From Stdlib Require Import Reals RIneq Ranalysis.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import Rfunctions.
From Stdlib Require Import Rseries.
From Stdlib Require Import SeqProp.
From Stdlib Require Import Compare_dec.

Open Scope R_scope.

(******************************************************************************)
(* 部分和与级数定义                                                            *)
(******************************************************************************)

Fixpoint partial_sum (a : nat -> R) (n : nat) : R :=
  match n with
  | 0%nat => a 0%nat
  | S k => partial_sum a k + a (S k)
  end.

Lemma partial_sum_S :
  forall (a : nat -> R) (n : nat),
    partial_sum a (S n) = partial_sum a n + a (S n).
Proof. intros. reflexivity. Qed.

Definition series_convergent (a : nat -> R) (L : R) : Prop :=
  Un_cv (fun n => partial_sum a n) L.

Definition series_cv (a : nat -> R) : Prop :=
  exists L : R, series_convergent a L.

Definition series_cauchy (a : nat -> R) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall m n : nat, (N <= n)%nat -> (n <= m)%nat ->
      Rabs (partial_sum a m - partial_sum a n) <= eps.

Definition absolutely_convergent (a : nat -> R) : Prop :=
  series_cv (fun n => Rabs (a n)).

Lemma half_gt_zero (eps : R) : eps > 0 -> eps / 2 > 0.
Proof.
  intro Heps. unfold Rdiv.
  assert (Hinv : / 2 > 0). { apply Rinv_0_lt_compat. lra. }
  assert (Hres := Rmult_lt_compat_l (/ 2) 0 eps Hinv Heps).
  rewrite Rmult_0_r in Hres. lra.
Qed.

Theorem series_convergent_iff_cauchy :
  forall (a : nat -> R), series_cv a <-> series_cauchy a.
Proof.
  intro a. split.
  - intros [L Hconv] eps Heps.
    pose proof (half_gt_zero eps Heps) as Hhalf.
    destruct (Hconv (eps / 2) Hhalf) as [N HN].
    exists N. intros m n Hn Hnm.
    assert (Hm : (N <= m)%nat) by lia.
    assert (Hm_abs : Rabs (partial_sum a m - L) < eps / 2).
    { specialize (HN m Hm). unfold Rdist in HN. exact HN. }
    assert (Hn_abs : Rabs (partial_sum a n - L) < eps / 2).
    { specialize (HN n Hn). unfold Rdist in HN. exact HN. }
    replace (partial_sum a m - partial_sum a n)
      with ((partial_sum a m - L) + - (partial_sum a n - L)) by lra.
    rewrite Rabs_Ropp.
    apply Rle_trans with (Rabs (partial_sum a m - L) + Rabs (partial_sum a n - L)).
    + apply Rabs_triang.
    + lra.
  - intros Hcauchy.
    assert (Hcauchy_seq : Cauchy_crit (fun n => partial_sum a n)).
    { unfold Cauchy_crit. intros eps Heps.
      specialize (Hcauchy (eps / 2) (half_gt_zero eps Heps)) as [N HN].
      exists N. intros n m Hn Hm.
      unfold Rdist.
      destruct (le_dec n m) as [Hle | Hgt].
      + specialize (HN m n Hn Hle). lra.
      + rewrite Rabs_Ropp. specialize (HN n m Hm Hgt). lra. }
    destruct (R_complete (fun n => partial_sum a n) Hcauchy_seq) as [L HL].
    exists L. exact HL.
Qed.

(******************************************************************************)
(* 引理：|partial_sum a m - partial_sum a n| <= partial_sum |a| m - partial_sum |a| n *)
(* 即 |∑_{k=n+1}^{m} a_k| <= ∑_{k=n+1}^{m} |a_k|                           *)
(* 由三角不等式和归纳                                                         *)
(******************************************************************************)

Lemma partial_sum_abs_le :
  forall (a : nat -> R) (n m : nat),
    (n <= m)%nat ->
    Rabs (partial_sum a m - partial_sum a n) <=
    partial_sum (fun k => Rabs (a k)) m - partial_sum (fun k => Rabs (a k)) n.
Proof.
  intros a n m Hnm.
  revert n Hnm.
  induction m as [|m IH].
  - intros n Hnm. simpl in Hnm. subst.
    assert (H1 : partial_sum a 0 - partial_sum a 0 = 0) by lra.
    assert (H2 : partial_sum (fun k => Rabs (a k)) 0 - partial_sum (fun k => Rabs (a k)) 0 = 0) by lra.
    rewrite H1. rewrite H2. rewrite Rabs_R0. lra.
  - intros n Hnm.
    destruct (Nat.eq_dec n (S m)) as [Heq | Hneq].
    + subst.
      assert (H1 : partial_sum a (S m) - partial_sum a (S m) = 0) by lra.
      assert (H2 : partial_sum (fun k => Rabs (a k)) (S m) - partial_sum (fun k => Rabs (a k)) (S m) = 0) by lra.
      rewrite H1. rewrite H2. rewrite Rabs_R0. lra.
    + assert (Hlt : (n <= m)%nat) by lia.
      specialize (IH n Hlt) as IH.
      assert (Hdiff_a : partial_sum a (S m) - partial_sum a n =
                        (partial_sum a m - partial_sum a n) + a (S m)) by lra.
      assert (Hdiff_abs : partial_sum (fun k => Rabs (a k)) (S m) - partial_sum (fun k => Rabs (a k)) n =
                          (partial_sum (fun k => Rabs (a k)) m - partial_sum (fun k => Rabs (a k)) n) + Rabs (a (S m))) by lra.
      rewrite Hdiff_a. rewrite Hdiff_abs.
      apply Rle_trans with (Rabs (partial_sum a m - partial_sum a n) + Rabs (a (S m))).
      * apply Rabs_triang.
      * assert (Habs_m : Rabs (a (S m)) <= Rabs (a (S m))) by apply Rle_refl.
        assert (Habs_diff : partial_sum (fun k => Rabs (a k)) m - partial_sum (fun k => Rabs (a k)) n >= 0).
        { apply Rle_ge. apply Rle_trans with (Rabs (partial_sum a m - partial_sum a n)).
          - exact IH.
          - apply Rabs_pos. }
        lra.
Qed.

(******************************************************************************)
(* 主定理：绝对收敛 ⟹ 收敛                                                   *)
(*                                                                            *)
(* 证明：∑|a_n| 收敛 ⟹ ∑|a_n| 是 Cauchy 级数                              *)
(* 由 partial_sum_abs_le: |S_m(a) - S_n(a)| <= S_m(|a|) - S_n(|a|) <= eps  *)
(* 所以 ∑a_n 也是 Cauchy 级数，由 R 完备性得收敛                            *)
(******************************************************************************)

Theorem absolutely_convergent_implies_convergent :
  forall (a : nat -> R),
    absolutely_convergent a -> series_cv a.
Proof.
  intros a Habs.
  apply series_convergent_iff_cauchy.
  intros eps Heps.
  assert (Habs_cauchy : series_cauchy (fun n => Rabs (a n))).
  { apply series_convergent_iff_cauchy. exact Habs. }
  specialize (Habs_cauchy eps Heps) as [N HN].
  exists N. intros m n Hn Hnm.
  apply Rle_trans with (partial_sum (fun k => Rabs (a k)) m - partial_sum (fun k => Rabs (a k)) n).
  - apply partial_sum_abs_le. exact Hnm.
  - exact (HN m n Hn Hnm).
Qed.
