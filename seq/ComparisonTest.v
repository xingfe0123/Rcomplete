From Stdlib Require Import Reals RIneq Ranalysis.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import Rfunctions.
From Stdlib Require Import Rseries.
From Stdlib Require Import SeqProp.

Open Scope R_scope.

(******************************************************************************)
(* 部分和定义：S_n = a_0 + a_1 + ... + a_n                                    *)
(******************************************************************************)

Fixpoint partial_sum (a : nat -> R) (n : nat) : R :=
  match n with
  | 0%nat => a 0%nat
  | S k => partial_sum a k + a (S k)
  end.

(******************************************************************************)
(* 级数收敛定义：部分和序列收敛                                                 *)
(******************************************************************************)

Definition series_convergent (a : nat -> R) (L : R) : Prop :=
  Un_cv (fun n => partial_sum a n) L.

Definition series_cv (a : nat -> R) : Prop :=
  exists L : R, series_convergent a L.

(******************************************************************************)
(* Cauchy 准则定义                                                              *)
(******************************************************************************)

Definition series_cauchy (a : nat -> R) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall m n : nat, (N <= n)%nat -> (n <= m)%nat ->
      Rabs (partial_sum a m - partial_sum a n) <= eps.

(******************************************************************************)
(* 引理：partial_sum 递推                                                      *)
(******************************************************************************)

Lemma partial_sum_S :
  forall (a : nat -> R) (n : nat),
    partial_sum a (S n) = partial_sum a n + a (S n).
Proof. intros. reflexivity. Qed.

(******************************************************************************)
(* 引理：eps/2 > 0                                                             *)
(******************************************************************************)

Lemma half_gt_zero (eps : R) : eps > 0 -> eps / 2 > 0.
Proof.
  intro Heps. unfold Rdiv.
  assert (Hinv : / 2 > 0). { apply Rinv_0_lt_compat. lra. }
  assert (Hres := Rmult_lt_compat_l (/ 2) 0 eps Hinv Heps).
  rewrite Rmult_0_r in Hres. lra.
Qed.

(******************************************************************************)
(* 引理：级数收敛 ⟺ Cauchy 准则                                                *)
(******************************************************************************)

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
(* 引理：部分和差 = 逐项求和 (归纳)                                            *)
(* S_m - S_n = a_{n+1} + a_{n+2} + ... + a_m  (当 m >= n)                   *)
(******************************************************************************)

Lemma partial_sum_diff_nonneg :
  forall (a : nat -> R) (n m : nat),
    (forall k : nat, (n < k)%nat -> (k <= m)%nat -> a k >= 0) ->
    (n <= m)%nat ->
    partial_sum a m - partial_sum a n >= 0.
Proof.
  intros a n m Hnneg Hnm.
  revert n Hnm Hnneg.
  induction m as [|m IH].
  - intros n Hnm Hnneg. simpl in Hnm. subst. lra.
  - intros n Hnm Hnneg.
    destruct (Nat.eq_dec n (S m)) as [Heq | Hneq].
    + subst. rewrite partial_sum_S.
      assert (H : a (S m) >= 0). { apply (Hnneg (S m)); lia. }
      lra.
    + assert (Hlt : (n <= m)%nat) by lia.
      assert (Hnneg' : forall k, (n < k)%nat -> (k <= m)%nat -> a k >= 0).
      { intros k Hkn Hkm. apply (Hnneg k); lia. }
      specialize (IH n Hlt Hnneg') as IH.
      rewrite partial_sum_S. rewrite partial_sum_S.
      assert (H : a (S m) >= 0). { apply (Hnneg (S m)); lia. }
      lra.
Qed.

(******************************************************************************)
(* 引理：|a_k| <= c_k 且 c_k >= 0 时                                          *)
(* |S_m(a) - S_n(a)| <= S_m(c) - S_n(c)                                      *)
(******************************************************************************)

Lemma partial_sum_abs_le :
  forall (a c : nat -> R) (n m : nat),
    (forall k : nat, Rabs (a k) <= c k) ->
    (forall k : nat, c k >= 0) ->
    (n <= m)%nat ->
    Rabs (partial_sum a m - partial_sum a n) <=
    partial_sum c m - partial_sum c n.
Proof.
  intros a c n m Habs Hcnneg Hnm.
  revert n Hnm.
  induction m as [|m IH].
  - intros n Hnm. simpl in Hnm. subst.
    assert (Ha : partial_sum a 0%nat - partial_sum a 0%nat = 0) by lra.
    assert (Hc : partial_sum c 0%nat - partial_sum c 0%nat = 0) by lra.
    rewrite Ha. rewrite Hc. rewrite Rabs_R0. lra.
  - intros n Hnm.
    destruct (Nat.eq_dec n (S m)) as [Heq | Hneq].
    + subst.
      assert (Ha : partial_sum a (S m) - partial_sum a (S m) = 0) by lra.
      assert (Hc : partial_sum c (S m) - partial_sum c (S m) = 0) by lra.
      rewrite Ha. rewrite Hc. rewrite Rabs_R0. lra.
    + assert (Hlt : (n <= m)%nat) by lia.
      specialize (IH n Hlt) as IH.
      assert (Hdiff_a : partial_sum a (S m) - partial_sum a n =
                        (partial_sum a m - partial_sum a n) + a (S m)) by lra.
      assert (Hdiff_c : partial_sum c (S m) - partial_sum c n =
                        (partial_sum c m - partial_sum c n) + c (S m)) by lra.
      rewrite Hdiff_a. rewrite Hdiff_c.
      apply Rle_trans with (Rabs (partial_sum a m - partial_sum a n) + Rabs (a (S m))).
      * apply Rabs_triang.
      * assert (Habs_m : Rabs (a (S m)) <= c (S m)). { apply Habs. }
        assert (Hc_m : c (S m) >= 0). { apply Hcnneg. }
        assert (Hc_diff : partial_sum c m - partial_sum c n >= 0).
        { apply partial_sum_diff_nonneg.
          - intros k Hkn Hkm. apply Hcnneg.
          - exact Hlt. }
        lra.
Qed.

(******************************************************************************)
(* 主定理：比较判别法                                                           *)
(* |a_n| <= c_n, c_n >= 0, sum c_n 收敛 => sum a_n 收敛                       *)
(******************************************************************************)

Theorem comparison_test :
  forall (a c : nat -> R),
    (forall n : nat, Rabs (a n) <= c n) ->
    (forall n : nat, c n >= 0) ->
    series_cv c ->
    series_cv a.
Proof.
  intros a c Habs Hcnneg Hcvc.
  apply series_convergent_iff_cauchy.
  intros eps Heps.
  assert (Hcauchy_c : series_cauchy c).
  { apply series_convergent_iff_cauchy. exact Hcvc. }
  specialize (Hcauchy_c eps Heps) as [N HN].
  exists N. intros m n Hn Hnm.
  apply Rle_trans with (partial_sum c m - partial_sum c n).
  - apply partial_sum_abs_le; [exact Habs | exact Hcnneg | exact Hnm].
  - exact (HN m n Hn Hnm).
Qed.
