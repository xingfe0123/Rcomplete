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
(* 部分和定义                                                                  *)
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

Lemma partial_sum_0 :
  forall (a : nat -> R), partial_sum a 0%nat = a 0%nat.
Proof. intros. reflexivity. Qed.

(******************************************************************************)
(* 分部求和核心引理                                                            *)
(*                                                                            *)
(* ∑_{k=m}^{n} a_k b_k = A_n b_n - A_{m-1} b_m + ∑_{k=m}^{n-1} A_k(b_k - b_{k+1}) *)
(* 其中 A_k = partial_sum a k                                                *)
(******************************************************************************)

(******************************************************************************)
(* 引理：partial_sum a k - partial_sum a (k-1) = a k (对 k >= 1)             *)
(******************************************************************************)

Lemma partial_sum_diff :
  forall (a : nat -> R) (k : nat),
    (0 < k)%nat ->
    partial_sum a k - partial_sum a (k - 1) = a k.
Proof.
  intros a k Hk.
  assert (H : k = S (k - 1)) by lia.
  rewrite H. rewrite partial_sum_S. lra.
Qed.

(******************************************************************************)
(* 更简洁的分部求和形式                                                        *)
(* ∑_{k=m}^{n} a_k b_k = A_n b_n - A_{m-1} b_m + ∑_{k=m}^{n-1} A_k(b_k - b_{k+1}) *)
(* 用递归定义从 m 到 n 的部分和                                               *)
(******************************************************************************)

Fixpoint sum_from (a : nat -> R) (m n : nat) : R :=
  match n - m with
  | 0%nat => a m
  | S k => a m + sum_from a (S m) n
  end.

Lemma sum_from_S :
  forall (a : nat -> R) (m n : nat),
    (m <= n)%nat ->
    sum_from a m (S n) = sum_from a m n + a (S n).
Proof.
  intros a m n Hmn.
  revert m Hmn.
  induction n as [|n IH].
  - intros m Hm. simpl in Hm. subst. simpl. lra.
  - intros m Hm.
    assert (Hm_n : (m <= n)%nat) by lia.
    specialize (IH m Hm_n).
    destruct (Nat.eq_dec m (S n)) as [Heq | Hneq].
    + subst. simpl. lra.
    + assert (Hdiff1 : S (S n) - m = S (S n - m)) by lia.
      assert (Hdiff2 : S n - m = S (n - m)) by lia.
      rewrite Hdiff1. rewrite Hdiff2.
      rewrite IH. lra.
Qed.

Lemma sum_from_eq_partial_sum :
  forall (a : nat -> R) (m n : nat),
    (m <= n)%nat ->
    sum_from a m n = partial_sum a n - partial_sum a (pred m).
Proof.
  intros a m n Hmn.
  revert m Hmn.
  induction n as [|n IH].
  - intros m Hm. simpl in Hm. subst. simpl. lra.
  - intros m Hm.
    destruct (Nat.eq_dec m (S n)) as [Heq | Hneq].
    + subst. simpl. rewrite partial_sum_S. lra.
    + assert (Hm_n : (m <= n)%nat) by lia.
      specialize (IH m Hm_n) as IH.
      rewrite sum_from_S by lia.
      rewrite partial_sum_S.
      rewrite IH.
      assert (Hm_pos : (0 < m)%nat) by lia.
      assert (Hpred_m : pred m = m - 1) by lia.
      rewrite Hpred_m. rewrite partial_sum_S. lra.
Qed.

(******************************************************************************)
(* 分部求和定理（一般形式）                                                    *)
(* ∑_{k=m}^{n} a_k b_k = A_n b_n - A_{m-1} b_m + ∑_{k=m}^{n-1} A_k(b_k - b_{k+1}) *)
(******************************************************************************)

Theorem summation_by_parts :
  forall (a b : nat -> R) (m n : nat),
    (0 < m)%nat -> (m <= n)%nat ->
    sum_from (fun k => a k * b k) m n =
    partial_sum a n * b n - partial_sum a (m - 1) * b m +
    sum_from (fun k => partial_sum a k * (b k - b (S k))) m (pred n).
Proof.
  intros a b m n Hm_pos Hmn.
  revert m Hm_pos Hmn.
  induction n as [|n IH].
  - intros m Hm Hmn. simpl in Hmn. subst. simpl. lra.
  - intros m Hm Hmn.
    destruct (Nat.eq_dec m (S n)) as [Heq | Hneq].
    + (* m = S n: 只有一项 *)
      subst. simpl. rewrite partial_sum_S. lra.
    + (* m < S n: 多项 *)
      assert (Hm_n : (m <= n)%nat) by lia.
      assert (Hm_pos2 : (0 < m)%nat) by lia.
      specialize (IH m Hm_pos2 Hm_n) as IH.
      rewrite (sum_from_S (fun k => a k * b k) m (S n)) by lia.
      rewrite IH.
      (* 右边也需要展开 *)
      rewrite (sum_from_S (fun k => partial_sum a k * (b k - b (S k))) m n) by lia.
      (* 目标：
         sum_from(a*b) m n + a(S n)*b(S n) =
         A_n * b_n - A_{m-1} * b_m + sum_from(A*(b-b')) m (pred n) + a(S n)*b(S n)
         
         由 IH: sum_from(a*b) m n = A_n * b_n - A_{m-1} * b_m + sum_from(A*(b-b')) m (pred n)
         
         但右边是 A_{Sn} * b_{Sn} - A_{m-1} * b_m + sum_from(A*(b-b')) m (pred(S n))
         = A_{Sn} * b_{Sn} - A_{m-1} * b_m + sum_from(A*(b-b')) m n
         = (A_n + a_{Sn}) * b_{Sn} - A_{m-1} * b_m + sum_from(A*(b-b')) m (pred n) + A_n*(b_n - b_{Sn})
         
         所以需要：
         A_n * b_n - A_{m-1} * b_m + sum_from(A*(b-b')) m (pred n) + a_{Sn}*b_{Sn}
         = (A_n + a_{Sn}) * b_{Sn} - A_{m-1} * b_m + sum_from(A*(b-b')) m (pred n) + A_n*(b_n - b_{Sn})
         
         即 A_n * b_n + a_{Sn}*b_{Sn} = A_n * b_{Sn} + a_{Sn}*b_{Sn} + A_n*(b_n - b_{Sn})
         即 A_n * b_n = A_n * b_{Sn} + A_n*(b_n - b_{Sn}) = A_n * b_n ✓
      *)
      rewrite partial_sum_S.
      assert (Hpred : pred (S n) = n) by lia.
      rewrite Hpred.
      assert (Hpred2 : pred n = n - 1) by lia.
      (* sum_from(A*(b-b')) m n = sum_from(A*(b-b')) m (pred n) + A_n*(b_n - b_{Sn}) *)
      assert (Hsum_split : sum_from (fun k => partial_sum a k * (b k - b (S k))) m n =
        sum_from (fun k => partial_sum a k * (b k - b (S k))) m (pred n) +
        partial_sum a n * (b n - b (S n))).
      { destruct (Nat.eq_dec m n) as [Heq2 | Hneq2].
        - (* m = n: sum_from m n = a_m, sum_from m (pred n) = a_m (pred n = m-1 < m) *)
          subst. simpl. lra.
        - (* m < n *)
          assert (Hm_lt_n : (m < n)%nat) by lia.
          rewrite sum_from_S by lia.
          assert (Hm_le_pred_n : (m <= pred n)%nat) by lia.
          rewrite sum_from_S by lia.
          lra. }
      rewrite Hsum_split. lra.
Qed.

(******************************************************************************)
(* 分部求和定理（从 0 开始）                                                  *)
(* ∑_{k=0}^{n} a_k b_k = A_n b_n + ∑_{k=0}^{n-1} A_k(b_k - b_{k+1})       *)
(******************************************************************************)

Theorem summation_by_parts_zero :
  forall (a b : nat -> R) (n : nat),
    partial_sum (fun k => a k * b k) n =
    partial_sum a n * b n +
    partial_sum (fun k => partial_sum a k * (b k - b (S k))) (pred n).
Proof.
  intros a b n.
  induction n as [|n IH].
  - (* n = 0 *)
    simpl. lra.
  - (* n = S n *)
    rewrite partial_sum_S. rewrite partial_sum_S.
    rewrite IH.
    (* IH: S_n(a*b) = A_n * b_n + S_{n-1}(A*(b-b')) *)
    (* 目标: S_n(a*b) + a_{Sn}*b_{Sn} = A_{Sn}*b_{Sn} + S_n(A*(b-b')) *)
    (* 其中 A_{Sn} = A_n + a_{Sn} *)
    (* S_n(A*(b-b')) = S_{n-1}(A*(b-b')) + A_n*(b_n - b_{Sn}) *)
    rewrite partial_sum_S.
    (* 现在目标:
       A_n * b_n + S_{n-1}(A*(b-b')) + a_{Sn}*b_{Sn}
       = (A_n + a_{Sn}) * b_{Sn} + S_{n-1}(A*(b-b')) + A_n*(b_n - b_{Sn})
       = A_n * b_{Sn} + a_{Sn}*b_{Sn} + S_{n-1}(A*(b-b')) + A_n*b_n - A_n*b_{Sn}
       化简: A_n * b_n + S_{n-1}(A*(b-b')) + a_{Sn}*b_{Sn}
           = A_n*b_n + a_{Sn}*b_{Sn} + S_{n-1}(A*(b-b'))  ✓
    *)
    lra.
Qed.

(******************************************************************************)
(* 应用 1：Dirichlet 判别法                                                   *)
(* 若 A_n = ∑_{k=0}^{n} a_k 有界，b_n 单调递减趋于 0                        *)
(* 则 ∑ a_n b_n 收敛                                                          *)
(******************************************************************************)

Definition series_cv (a : nat -> R) : Prop :=
  exists L : R, Un_cv (fun n => partial_sum a n) L.

Definition series_cauchy (a : nat -> R) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall m n : nat, (N <= n)%nat -> (n <= m)%nat ->
      Rabs (partial_sum a m - partial_sum a n) <= eps.

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
(* (D) 单调递减序列趋于 0 的性质                                              *)
(******************************************************************************)

Axiom decreasing_tendsto_0 :
  forall (b : nat -> R),
    Un_growing (fun n => - b n) -> Un_cv b 0 ->
    forall eps, eps > 0 -> exists N, forall n, (N <= n)%nat -> Rabs (b n) < eps.

(******************************************************************************)
(* (D) 有界序列的定义和性质                                                   *)
(******************************************************************************)

Definition bounded_seq (a : nat -> R) : Prop :=
  exists M : R, M > 0 /\ forall n, Rabs (a n) <= M.

(******************************************************************************)
(* Dirichlet 判别法                                                            *)
(* 若 A_n = ∑_{k=0}^{n} a_k 有界，b_n 单调递减趋于 0                        *)
(* 则 ∑ a_n b_n 收敛                                                          *)
(******************************************************************************)

Theorem dirichlet_test :
  forall (a b : nat -> R),
    bounded_seq (fun n => partial_sum a n) ->
    Un_growing (fun n => - b n) ->
    Un_cv b 0 ->
    series_cv (fun n => a n * b n).
Admitted.

(******************************************************************************)
(* 应用 2：Abel 判别法                                                        *)
(* 若 ∑ a_n 收敛，b_n 单调有界                                               *)
(* 则 ∑ a_n b_n 收敛                                                          *)
(******************************************************************************)

Theorem abel_test :
  forall (a b : nat -> R),
    series_cv a ->
    Un_growing (fun n => - b n) \/ Un_growing b ->
    bounded_seq b ->
    series_cv (fun n => a n * b n).
Admitted.

(******************************************************************************)
(* 应用 3：Abel 变换用于交错级数                                              *)
(* 若 b_n 单调递减趋于 0，则 ∑ (-1)^n b_n 收敛                              *)
(******************************************************************************)

Axiom alternating_series_test :
  forall (b : nat -> R),
    Un_growing (fun n => - b n) ->
    Un_cv b 0 ->
    series_cv (fun n => (-1) ^ n * b n).
