From Stdlib Require Import Reals RIneq Ranalysis.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
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
(* 对任意 eps > 0, 存在 N, m >= n >= N 时 |S_m - S_n| <= eps                  *)
(* 其中 S_m - S_n = sum_{k=n+1}^{m} a_k                                      *)
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
Proof.
  intros. reflexivity.
Qed.

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
(* 主定理：级数收敛 ⟺ Cauchy 准则                                              *)
(******************************************************************************)

Theorem series_convergent_iff_cauchy :
  forall (a : nat -> R), series_cv a <-> series_cauchy a.
Proof.
  intro a. split.
  - (* 收敛 ⟹ Cauchy *)
    intros [L Hconv] eps Heps.
    pose proof (half_gt_zero eps Heps) as Hhalf.
    destruct (Hconv (eps / 2) Hhalf) as [N HN].
    exists N. intros m n Hn Hnm.
    (* |S_m - S_n| = |(S_m - L) - (S_n - L)| <= |S_m - L| + |S_n - L| *)
    assert (Hm : (N <= m)%nat) by lia.
    assert (Hdiff : partial_sum a m - partial_sum a n =
                    (partial_sum a m - L) - (partial_sum a n - L)) by lra.
    rewrite Hdiff.
    assert (Hm_abs : Rabs (partial_sum a m - L) < eps / 2).
    { specialize (HN m Hm). unfold Rdist in HN. exact HN. }
    assert (Hn_abs : Rabs (partial_sum a n - L) < eps / 2).
    { specialize (HN n Hn). unfold Rdist in HN. exact HN. }
    (* |S_m - S_n| = |(S_m - L) + -(S_n - L)| <= |S_m - L| + |-(S_n - L)| = |S_m - L| + |S_n - L| < eps *)
    replace (partial_sum a m - partial_sum a n)
      with ((partial_sum a m - L) + - (partial_sum a n - L)) by lra.
    rewrite Rabs_Ropp.
    apply Rle_trans with (Rabs (partial_sum a m - L) + Rabs (partial_sum a n - L)).
    + apply Rabs_triang.
    + lra.
  - (* Cauchy ⟹ 收敛 *)
    intros Hcauchy.
    (* 证明部分和序列是 Cauchy 列 *)
    assert (Hcauchy_seq : Cauchy_crit (fun n => partial_sum a n)).
    { unfold Cauchy_crit. intros eps Heps.
      specialize (Hcauchy (eps / 2) (half_gt_zero eps Heps)) as [N HN].
      exists N. intros n m Hn Hm.
      unfold Rdist.
      destruct (le_dec n m) as [Hle | Hgt].
      + (* n <= m *)
        specialize (HN m n Hn Hle).
        lra.
      + (* m < n *)
        rewrite Rabs_Ropp.
        specialize (HN n m Hm Hgt).
        lra. }
    (* 由 R 完备性，Cauchy 列收敛 *)
    destruct (R_complete (fun n => partial_sum a n) Hcauchy_seq) as [L HL].
    exists L. exact HL.
Qed.
