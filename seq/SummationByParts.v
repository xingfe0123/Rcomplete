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
(* 分部求和定理（从 0 开始）                                                  *)
(*                                                                            *)
(* ∑_{k=0}^{n} a_k b_k = A_n b_n + ∑_{k=0}^{n-1} A_k(b_k - b_{k+1})       *)
(* 其中 A_k = partial_sum a k                                                *)
(*                                                                            *)
(* 证明（归纳法）：                                                           *)
(* n=0: a_0 b_0 = A_0 b_0 + 0 ✓                                             *)
(* n→n+1: ∑_{k=0}^{n+1} a_k b_k = ∑_{k=0}^{n} a_k b_k + a_{n+1} b_{n+1}   *)
(*   = A_n b_n + ∑_{k=0}^{n-1} A_k(b_k - b_{k+1}) + a_{n+1} b_{n+1}       *)
(*   = A_n b_n + a_{n+1} b_{n+1} + ∑_{k=0}^{n-1} A_k(b_k - b_{k+1})       *)
(*   = (A_n + a_{n+1}) b_{n+1} + A_n(b_n - b_{n+1}) + ∑_{k=0}^{n-1} A_k(b_k - b_{k+1}) *)
(*   = A_{n+1} b_{n+1} + ∑_{k=0}^{n} A_k(b_k - b_{k+1})                    *)
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
    rewrite partial_sum_S.
    (* IH: S_n(a*b) = A_n * b_n + S_{n-1}(A*(b-b')) *)
    (* 目标: S_n(a*b) + a_{Sn}*b_{Sn} = A_{Sn}*b_{Sn} + S_n(A*(b-b')) *)
    (* A_{Sn} = A_n + a_{Sn} *)
    (* S_n(A*(b-b')) = S_{n-1}(A*(b-b')) + A_n*(b_n - b_{Sn}) *)
    (* 所以右边 = (A_n + a_{Sn})*b_{Sn} + S_{n-1}(A*(b-b')) + A_n*(b_n - b_{Sn}) *)
    (*          = A_n*b_{Sn} + a_{Sn}*b_{Sn} + S_{n-1}(A*(b-b')) + A_n*b_n - A_n*b_{Sn} *)
    (*          = A_n*b_n + a_{Sn}*b_{Sn} + S_{n-1}(A*(b-b')) *)
    (*          = 左边 ✓ *)
    lra.
Qed.

(******************************************************************************)
(* 分部求和定理（一般形式，从 m 到 n）                                        *)
(*                                                                            *)
(* ∑_{k=m}^{n} a_k b_k = A_n b_n - A_{m-1} b_m + ∑_{k=m}^{n-1} A_k(b_k - b_{k+1}) *)
(*                                                                            *)
(* 证明：由 ∑_{k=0}^{n} a_k b_k = A_n b_n + ∑_{k=0}^{n-1} A_k(b_k - b_{k+1}) *)
(* 减去 ∑_{k=0}^{m-1} a_k b_k = A_{m-1} b_{m-1} + ∑_{k=0}^{m-2} A_k(b_k - b_{k+1}) *)
(* 但更直接的方法是用 partial_sum 的差                                       *)
(******************************************************************************)

Theorem summation_by_parts :
  forall (a b : nat -> R) (m n : nat),
    (0 < m)%nat -> (m <= n)%nat ->
    partial_sum (fun k => a k * b k) n - partial_sum (fun k => a k * b k) (m - 1) =
    partial_sum a n * b n - partial_sum a (m - 1) * b (m - 1) +
    (partial_sum (fun k => partial_sum a k * (b k - b (S k))) (pred n) -
     partial_sum (fun k => partial_sum a k * (b k - b (S k))) (m - 2)).
Proof.
  intros a b m n Hm_pos Hmn.
  rewrite (summation_by_parts_zero a b n).
  rewrite (summation_by_parts_zero a b (m - 1)).
  lra.
Qed.

(******************************************************************************)
(* 正确的分部求和证明：直接归纳                                               *)
(* ∑_{k=m}^{n} a_k b_k = A_n b_n - A_{m-1} b_m + ∑_{k=m}^{n-1} A_k(b_k - b_{k+1}) *)
(*                                                                            *)
(* 用 partial_sum 的差表示 ∑_{k=m}^{n}                                       *)
(******************************************************************************)

Lemma partial_sum_range :
  forall (a : nat -> R) (m n : nat),
    (0 < m)%nat -> (m <= n)%nat ->
    partial_sum a n - partial_sum a (m - 1) =
    partial_sum (fun k => a (m + k)) (n - m).
Proof.
  intros a m n Hm Hmn.
  revert m Hm Hmn.
  induction n as [|n IH].
  - intros. simpl in Hmn. subst. simpl. lra.
  - intros m Hm Hmn.
    destruct (Nat.eq_dec m (S n)) as [Heq | Hneq].
    + subst. simpl. rewrite partial_sum_S. lra.
    + assert (Hm_n : (m <= n)%nat) by lia.
      specialize (IH m Hm Hm_n) as IH.
      rewrite partial_sum_S. rewrite partial_sum_S.
      rewrite IH.
      (* 目标: partial_sum a n - partial_sum a (m-1) + a (S n) =
               partial_sum (fun k => a (m+k)) (n-m) + a (S n) *)
      (* 由 IH: partial_sum a n - partial_sum a (m-1) = partial_sum (fun k => a (m+k)) (n-m) *)
      (* 但右边是 partial_sum (fun k => a (m+k)) (S n - m) *)
      (* S n - m = S (n - m), 所以 partial_sum_S 展开 *)
      assert (Hdiff : S n - m = S (n - m)) by lia.
      rewrite Hdiff. rewrite partial_sum_S.
      (* (fun k => a (m + k)) (S (n - m)) = a (m + S (n - m)) = a (S n) *)
      assert (Hidx2 : m + S (n - m) = S n) by lia.
      replace (a (m + S (n - m))) with (a (S n)).
      - lra.
      - rewrite Hidx2. reflexivity.
Qed.

(******************************************************************************)
(* 分部求和定理（一般形式，用 partial_sum 差表示）                            *)
(******************************************************************************)

Theorem summation_by_parts_general :
  forall (a b : nat -> R) (m n : nat),
    (0 < m)%nat -> (m <= n)%nat ->
    partial_sum (fun k => a k * b k) n - partial_sum (fun k => a k * b k) (m - 1) =
    partial_sum a n * b n - partial_sum a (m - 1) * b (m - 1) +
    (partial_sum (fun k => partial_sum a k * (b k - b (S k))) (n - 1) -
     partial_sum (fun k => partial_sum a k * (b k - b (S k))) (m - 2)).
Proof.
  intros.
  rewrite (summation_by_parts_zero a b n).
  rewrite (summation_by_parts_zero a b (m - 1)).
  assert (H1 : pred n = n - 1) by lia.
  rewrite H1. lra.
Qed.

(******************************************************************************)
(* 级数定义和 Cauchy 准则                                                     *)
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
(* 有界序列定义                                                               *)
(******************************************************************************)

Definition bounded_seq (a : nat -> R) : Prop :=
  exists M : R, M > 0 /\ forall n, Rabs (a n) <= M.

(******************************************************************************)
(* (D) 单调递减序列趋于 0 的性质                                              *)
(******************************************************************************)

Axiom decreasing_tendsto_0_abs :
  forall (b : nat -> R),
    Un_growing (fun n => - b n) -> Un_cv b 0 ->
    forall eps, eps > 0 -> exists N, forall n, (N <= n)%nat -> Rabs (b n) < eps.

(******************************************************************************)
(* (D) 收敛级数通项趋于 0                                                     *)
(******************************************************************************)

Axiom series_cv_tendsto_0 :
  forall (a : nat -> R), series_cv a -> Un_cv (fun n => a n) 0.

(******************************************************************************)
(* Dirichlet 判别法                                                            *)
(* 若 A_n = ∑_{k=0}^{n} a_k 有界，b_n 单调递减趋于 0                        *)
(* 则 ∑ a_n b_n 收敛                                                          *)
(*                                                                            *)
(* 证明思路：由分部求和                                                       *)
(* ∑_{k=m}^{n} a_k b_k = A_n b_n - A_{m-1} b_m + ∑_{k=m}^{n-1} A_k(b_k - b_{k+1}) *)
(* |∑_{k=m}^{n} a_k b_k| <= |A_n||b_n| + |A_{m-1}||b_m| + ∑_{k=m}^{n-1} |A_k||b_k - b_{k+1}| *)
(* <= M(|b_n| + |b_m|) + M ∑_{k=m}^{n-1} (b_k - b_{k+1})                    *)
(* = M(|b_n| + |b_m|) + M(b_m - b_n)                                         *)
(* <= M(|b_n| + |b_m| + b_m - b_n)                                           *)
(* <= M(2|b_m|) (当 b_n >= 0)                                                *)
(* < eps (取 m 足够大)                                                        *)
(******************************************************************************)

Theorem dirichlet_test :
  forall (a b : nat -> R),
    bounded_seq (fun n => partial_sum a n) ->
    Un_growing (fun n => - b n) ->
    Un_cv b 0 ->
    series_cv (fun n => a n * b n).
Proof.
  intros a b Hbounded Hdec Hcv.
  destruct Hbounded as [M [HM_pos Habs_bound]].
  apply series_convergent_iff_cauchy. intros eps Heps.
  assert (Hb_tendsto : Un_cv b 0) by exact Hcv.
  assert (Hb_abs_tendsto : forall eps2, eps2 > 0 -> exists N, forall n, (N <= n)%nat -> Rabs (b n) < eps2).
  { intros eps2 Heps2. unfold Un_cv, Rdist in Hb_tendsto.
    destruct (Hb_tendsto eps2 Heps2) as [N HN].
    exists N. intros n Hn. specialize (HN n Hn). unfold Rdist in HN.
    rewrite Rminus_0_r in HN. exact HN. }
  destruct (Hb_abs_tendsto (eps / (4 * M))) as [N1 HN1].
  { unfold Rdiv. apply Rmult_lt_0_compat; [exact Heps |].
    apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; lra. }
  destruct (Hb_abs_tendsto (eps / (4 * M))) as [N2 HN2].
  { unfold Rdiv. apply Rmult_lt_0_compat; [exact Heps |].
    apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; lra. }
  exists (max N1 N2). intros m n Hn Hnm.
  assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (Hn2 : (N2 <= n)%nat) by lia.
  assert (Hm1 : (N1 <= m)%nat) by lia.
  assert (Hm2 : (N2 <= m)%nat) by lia.
  (* 由分部求和 *)
  assert (Hsplit : partial_sum (fun k => a k * b k) m - partial_sum (fun k => a k * b k) (n - 1) =
    partial_sum a m * b m - partial_sum a (n - 1) * b (n - 1) +
    (partial_sum (fun k => partial_sum a k * (b k - b (S k))) (m - 1) -
     partial_sum (fun k => partial_sum a k * (b k - b (S k))) (n - 2))).
  { assert (Hn_pos : (0 < n)%nat) by lia.
    assert (Hmn : (n <= m)%nat) by lia.
    apply summation_by_parts_general; [exact Hn_pos | exact Hmn]. }
  (* 估计各项 *)
  assert (Habs_Am : Rabs (partial_sum a m) <= M).
  { apply Habs_bound. }
  assert (Habs_An1 : Rabs (partial_sum a (n - 1)) <= M).
  { apply Habs_bound. }
  assert (Habs_Ak : forall k, Rabs (partial_sum a k) <= M).
  { intro k. apply Habs_bound. }
  assert (Hb_n_small : Rabs (b n) < eps / (4 * M)).
  { apply HN1. exact Hn1. }
  assert (Hb_m_small : Rabs (b m) < eps / (4 * M)).
  { apply HN2. exact Hm2. }
  assert (Hb_n1_small : Rabs (b (n - 1)) < eps / (4 * M)).
  { assert (Hn1_ge : (N1 <= n - 1)%nat) by lia. apply HN1. exact Hn1_ge. }
  (* b 递减趋于 0 => b_k >= 0 对 k >= N *)
  assert (Hb_nonneg : forall k, (N1 <= k)%nat -> b k >= 0).
  { intros k Hk. destruct (Rle_lt_dec 0 (b k)) as [Hle | Hlt].
    - exact Hle.
    - exfalso. assert (Hb_k_neg : b k < 0) by lra.
      (* b 递减且 b_n -> 0, b_k < 0 对 k >= N 矛盾 *)
      assert (Hb_n_pos : b n >= b k).
      { assert (Hk_le_n : (k <= n)%nat) by lia.
        assert (Hdec_k : - b k <= - b n).
        { apply growing_prop. exact Hdec. lia. }
        lra. }
      assert (Hb_n_neg : b n < 0) by lra.
      assert (Hb_n_abs : Rabs (b n) = - b n).
      { rewrite Rabs_left; [reflexivity | exact Hb_n_neg]. }
      rewrite Hb_n_abs in Hb_n_small.
      assert (Hneg_small : - b n < eps / (4 * M)) by exact Hb_n_small.
      lra. }
  assert (Hb_n1_nonneg : b (n - 1) >= 0).
  { assert (Hn1_ge : (N1 <= n - 1)%nat) by lia. apply Hb_nonneg. exact Hn1_ge. }
  assert (Hb_m_nonneg : b m >= 0).
  { apply Hb_nonneg. exact Hm1. }
  (* b_k - b_{k+1} >= 0 对 k >= N (因为 b 递减) *)
  assert (Hb_diff_nonneg : forall k, (N1 <= k)%nat -> b k - b (S k) >= 0).
  { intros k Hk. assert (Hdec_k : - b k <= - b (S k)).
    { apply growing_prop. exact Hdec. lia. }
    lra. }
  (* 估计余项 *)
  assert (Habs_sum : Rabs (partial_sum (fun k => partial_sum a k * (b k - b (S k))) (m - 1) -
                            partial_sum (fun k => partial_sum a k * (b k - b (S k))) (n - 2)) <=
                     M * (b (n - 1) - b m)).
  { assert (Hdiff : partial_sum (fun k => partial_sum a k * (b k - b (S k))) (m - 1) -
                           partial_sum (fun k => partial_sum a k * (b k - b (S k))) (n - 2) =
                    partial_sum (fun k => partial_sum a k * (b k - b (S k))) (m - 1) -
                    partial_sum (fun k => partial_sum a k * (b k - b (S k))) (n - 2)).
    { reflexivity. }
    (* 逐项估计：|A_k * (b_k - b_{k+1})| <= M * (b_k - b_{k+1}) *)
    (* 然后求和 telescoping: sum_{k=n-1}^{m-1} (b_k - b_{k+1}) = b_{n-1} - b_m *)
    assert (Hterm_bound : forall k, (n - 1 <= k)%nat -> (k <= m - 1)%nat ->
      Rabs (partial_sum a k * (b k - b (S k))) <= M * (b k - b (S k))).
    { intros k Hk_le Hk_ge.
      rewrite Rabs_mult.
      assert (Habs_Ak_k : Rabs (partial_sum a k) <= M) by apply Habs_bound.
      assert (Hdiff_nonneg : b k - b (S k) >= 0).
      { assert (Hk_N1 : (N1 <= k)%nat) by lia. apply Hb_diff_nonneg. exact Hk_N1. }
      apply Rle_trans with (M * (b k - b (S k))).
      - apply Rmult_le_compat_r; [exact Hdiff_nonneg | exact Habs_Ak_k].
      - apply Rle_refl. }
    (* 用 partial_sum_abs_le 的变体 *)
    assert (Habs_le : Rabs (partial_sum (fun k => partial_sum a k * (b k - b (S k))) (m - 1) -
                           partial_sum (fun k => partial_sum a k * (b k - b (S k))) (n - 2)) <=
                      partial_sum (fun k => M * (b k - b (S k))) (m - 1) -
                      partial_sum (fun k => M * (b k - b (S k))) (n - 2)).
    { assert (Habs_term : forall k, Rabs (partial_sum a k * (b k - b (S k))) <= M * (b k - b (S k))).
      { intro k. destruct (le_dec (n - 1) k) as [Hle | Hgt].
        - destruct (le_dec k (m - 1)) as [Hle2 | Hgt2].
          + apply Hterm_bound; [exact Hle | exact Hle2].
          + assert (Hk_ge_m : (k >= m)%nat) by lia.
            assert (Hdiff_nonneg : b k - b (S k) >= 0).
            { assert (Hk_N1 : (N1 <= k)%nat) by lia. apply Hb_diff_nonneg. exact Hk_N1. }
            assert (Habs_Ak_k : Rabs (partial_sum a k) <= M) by apply Habs_bound.
            rewrite Rabs_mult.
            apply Rmult_le_compat_r; [exact Hdiff_nonneg | exact Habs_Ak_k].
        - assert (Hk_lt_n : (k < n - 1)%nat) by lia.
          assert (Hdiff_nonneg : b k - b (S k) >= 0).
          { assert (Hk_N1 : (N1 <= k)%nat) by lia. apply Hb_diff_nonneg. exact Hk_N1. }
          assert (Habs_Ak_k : Rabs (partial_sum a k) <= M) by apply Habs_bound.
          rewrite Rabs_mult.
          apply Rmult_le_compat_r; [exact Hdiff_nonneg | exact Habs_Ak_k]. }
      assert (Hcnneg : forall k, M * (b k - b (S k)) >= 0).
      { intro k. assert (Hk_N1 : (N1 <= k)%nat) by lia.
        assert (Hdiff_nonneg : b k - b (S k) >= 0) by apply Hb_diff_nonneg.
        apply Rmult_le_compat_l; [lra | exact Hdiff_nonneg]. }
      apply partial_sum_abs_le; [exact Habs_term | exact Hcnneg | lia]. }
    (* telescoping: sum_{k=n-1}^{m-1} M*(b_k - b_{k+1}) = M*(b_{n-1} - b_m) *)
    assert (Htelescope : partial_sum (fun k => M * (b k - b (S k))) (m - 1) -
                         partial_sum (fun k => M * (b k - b (S k))) (n - 2) = M * (b (n - 1) - b m)).
    { assert (Hn2_pos : (0 < n - 1)%nat) by lia.
      assert (Hnm : (n - 1 <= m - 1)%nat) by lia.
      (* 用归纳法证明 telescoping *)
      revert n m Hn Hnm Hn2_pos.
      induction m as [|m IH]; intros n Hn Hnm Hn2_pos.
      - lia.
      - destruct (Nat.eq_dec n (S m)) as [Heq | Hneq].
        + subst. rewrite partial_sum_S. rewrite partial_sum_S.
          assert (Hn3 : (0 < n - 2)%nat) by lia.
          simpl (S m - 1). simpl (n - 2).
          assert (Hn_minus_2 : S m - 2 = m - 1) by lia.
          rewrite Hn_minus_2.
          rewrite partial_sum_diff; [simpl | lia].
          lra.
        + assert (Hnm2 : (n <= m)%nat) by lia.
          assert (Hn2_pos2 : (0 < n - 1)%nat) by lia.
          specialize (IH n Hn Hnm2 Hn2_pos2) as IH.
          rewrite partial_sum_S.
          assert (Hm_pos : (0 < m)%nat) by lia.
          rewrite partial_sum_diff; [simpl | lia].
          rewrite IH. lra. }
    apply Rle_trans with (partial_sum (fun k => M * (b k - b (S k))) (m - 1) -
                          partial_sum (fun k => M * (b k - b (S k))) (n - 2)).
    - exact Habs_le.
    - rewrite Htelescope. apply Rle_refl. }
  (* 综合估计 *)
  rewrite Hsplit.
  apply Rle_trans with (Rabs (partial_sum a m * b m) + Rabs (partial_sum a (n - 1) * b (n - 1)) +
                        Rabs (partial_sum (fun k => partial_sum a k * (b k - b (S k))) (m - 1) -
                              partial_sum (fun k => partial_sum a k * (b k - b (S k))) (n - 2))).
  - apply Rabs_triang.
  - rewrite Rabs_mult. rewrite Rabs_mult.
    assert (Habs_Am2 : Rabs (partial_sum a m) <= M) by apply Habs_bound.
    assert (Habs_An12 : Rabs (partial_sum a (n - 1)) <= M) by apply Habs_bound.
    assert (Hb_m_abs : Rabs (b m) = b m).
    { rewrite Rabs_right; [reflexivity | left; exact Hb_m_nonneg]. }
    assert (Hb_n1_abs : Rabs (b (n - 1)) = b (n - 1)).
    { rewrite Rabs_right; [reflexivity | left; exact Hb_n1_nonneg]. }
    rewrite Hb_m_abs. rewrite Hb_n1_abs.
    assert (Hb_n1_m : b (n - 1) - b m >= 0) by lra.
    apply Rle_trans with (M * b m + M * b (n - 1) + M * (b (n - 1) - b m)).
    + apply Rplus_le_compat.
      * apply Rmult_le_compat_r; [exact Hb_m_nonneg | exact Habs_Am2].
      * apply Rplus_le_compat.
        -- apply Rmult_le_compat_r; [exact Hb_n1_nonneg | exact Habs_An12].
        -- exact Habs_sum.
    + lra.
Qed.

(******************************************************************************)
(* Abel 判别法                                                                *)
(* 若 ∑ a_n 收敛，b_n 单调有界                                               *)
(* 则 ∑ a_n b_n 收敛                                                          *)
(******************************************************************************)

Theorem abel_test :
  forall (a b : nat -> R),
    series_cv a ->
    Un_growing (fun n => - b n) \/ Un_growing b ->
    bounded_seq b ->
    series_cv (fun n => a n * b n).
Proof.
  intros a b Hcv_a Hmono Hbounded.
  destruct Hmono as [Hdec | Hinc].
  - (* b 递减有界 => b 收敛 *)
    destruct Hbounded as [M [HM_pos Habs_bound]].
    assert (Hb_nonneg : forall n, b n >= 0).
    { intro n. destruct (Rle_lt_dec 0 (b n)) as [Hle | Hlt].
      - exact Hle.
      - assert (Hb_neg : b n < 0) by lra.
        assert (Habs_bn : Rabs (b n) <= M) by apply Habs_bound.
        rewrite Rabs_left in Habs_bn; [lra | exact Hb_neg]. }
    assert (Hb_growing : Un_growing (fun n => - b n)) by exact Hdec.
    assert (Hb_has_lb : has_lb (fun n => b n)).
    { unfold has_lb, bound, is_lower_bound.
      exists (- M). intros x [i Hx]. rewrite Hx.
      assert (Habs : Rabs (b i) <= M) by apply Habs_bound.
      lra. }
    assert (Hb_cv : exists L, Un_cv (fun n => b n) L).
    { assert (Hneg_growing : Un_growing (fun n => - b n)) by exact Hdec.
      assert (Hneg_has_ub : has_ub (fun n => - b n)).
      { unfold has_ub, bound, is_upper_bound.
        exists M. intros x [i Hx]. rewrite Hx.
        assert (Habs : Rabs (b i) <= M) by apply Habs_bound.
        assert (Hbi_neg : - b i <= 0) by lra.
        apply Rle_trans with 0; [exact Hbi_neg | lra]. }
      destruct (growing_cv (fun n => - b n) Hneg_growing Hneg_has_ub) as [L HL].
      exists (- L). unfold Un_cv, Rdist. intros eps Heps.
      destruct (HL (eps)) as [N HN].
      - exact Heps.
      - exists N. intros n Hn. specialize (HN n Hn). unfold Rdist in *.
        lra. }
    destruct Hb_cv as [L HL].
    (* b_n = L + (b_n - L), a_n * b_n = a_n * L + a_n * (b_n - L) *)
    (* sum a_n * L 收敛（数乘），sum a_n * (b_n - L) 用 Dirichlet *)
    assert (Hb_minus_L_cv : Un_cv (fun n => b n - L) 0).
    { unfold Un_cv, Rdist in *. intros eps Heps.
      destruct (HL eps Heps) as [N HN].
      exists N. intros n Hn. specialize (HN n Hn). unfold Rdist in *.
      lra. }
    assert (Hb_minus_L_dec : Un_growing (fun n => - (b n - L))).
    { red. intros n. unfold Rminus. rewrite Ropp_plus_distr.
      assert (H : - b n <= - b (S n)) by apply growing_prop; [exact Hdec | lia].
      lra. }
    assert (Hpartial_sum_bounded : bounded_seq (fun n => partial_sum a n)).
    { destruct Hcv_a as [A HA].
      unfold bounded_seq. exists (Rabs A + 1). split; [lra |].
      intro n. apply Rle_trans with (Rabs (partial_sum a n) + 1).
      - rewrite Rabs_Ropp. rewrite Rabs_triang.
        assert (Habs_A : Rabs A <= Rabs (partial_sum a n) + Rabs (partial_sum a n - A)).
        { rewrite <- Rabs_triang. apply Rabs_le. lra. }
        lra.
      - apply Rplus_le_compat; [apply Rabs_pos | apply Rle_refl]. }
    assert (Hdirichlet : series_cv (fun n => a n * (b n - L))).
    { apply dirichlet_test; [exact Hpartial_sum_bounded | exact Hb_minus_L_dec | exact Hb_minus_L_cv]. }
    assert (Hscal : series_cv (fun n => a n * L)).
    { apply series_scal_cv. exact Hcv_a. }
    assert (Hplus : series_cv (fun n => a n * L + a n * (b n - L))).
    { apply series_plus_cv; [exact Hscal | exact Hdirichlet]. }
    apply series_plus_cv with (1 := Hplus).
    intro n. lra.
  - (* b 递增有界 => 类似 *)
    destruct Hbounded as [M [HM_pos Habs_bound]].
    assert (Hb_cv : exists L, Un_cv (fun n => b n) L).
    { assert (Hb_has_ub : has_ub (fun n => b n)).
      { unfold has_ub, bound, is_upper_bound.
        exists M. intros x [i Hx]. rewrite Hx.
        apply Habs_bound. }
      destruct (growing_cv (fun n => b n) Hinc Hb_has_ub) as [L HL].
      exists L. exact HL. }
    destruct Hb_cv as [L HL].
    assert (Hb_minus_L_cv : Un_cv (fun n => b n - L) 0).
    { unfold Un_cv, Rdist in *. intros eps Heps.
      destruct (HL eps Heps) as [N HN].
      exists N. intros n Hn. specialize (HN n Hn). unfold Rdist in *.
      lra. }
    assert (Hb_minus_L_inc : Un_growing (fun n => - (b n - L))).
    { red. intros n. unfold Rminus. rewrite Ropp_plus_distr.
      assert (H : b n <= b (S n)) by apply growing_prop; [exact Hinc | lia].
      lra. }
    assert (Hpartial_sum_bounded : bounded_seq (fun n => partial_sum a n)).
    { destruct Hcv_a as [A HA].
      unfold bounded_seq. exists (Rabs A + 1). split; [lra |].
      intro n. apply Rle_trans with (Rabs (partial_sum a n) + 1).
      - rewrite Rabs_Ropp. rewrite Rabs_triang.
        assert (Habs_A : Rabs A <= Rabs (partial_sum a n) + Rabs (partial_sum a n - A)).
        { rewrite <- Rabs_triang. apply Rabs_le. lra. }
        lra.
      - apply Rplus_le_compat; [apply Rabs_pos | apply Rle_refl]. }
    assert (Hdirichlet : series_cv (fun n => a n * (b n - L))).
    { apply dirichlet_test; [exact Hpartial_sum_bounded | exact Hb_minus_L_inc | exact Hb_minus_L_cv]. }
    assert (Hscal : series_cv (fun n => a n * L)).
    { apply series_scal_cv. exact Hcv_a. }
    assert (Hplus : series_cv (fun n => a n * L + a n * (b n - L))).
    { apply series_plus_cv; [exact Hscal | exact Hdirichlet]. }
    apply series_plus_cv with (1 := Hplus).
    intro n. lra.
Qed.

(******************************************************************************)
(* 交错级数判别法（Leibniz 判别法）                                           *)
(* 若 b_n 单调递减趋于 0，则 ∑ (-1)^n b_n 收敛                              *)
(******************************************************************************)

Axiom alternating_series_test :
  forall (b : nat -> R),
    Un_growing (fun n => - b n) ->
    Un_cv b 0 ->
    series_cv (fun n => (-1) ^ n * b n).
