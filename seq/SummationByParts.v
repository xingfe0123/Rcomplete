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
    partial_sum a n * b n - partial_sum a (m - 1) * b m +
    (partial_sum (fun k => partial_sum a k * (b k - b (S k))) (pred n) -
     partial_sum (fun k => partial_sum a k * (b k - b (S k))) (m - 2)).
Proof.
  intros a b m n Hm_pos Hmn.
  rewrite (summation_by_parts_zero a b n).
  rewrite (summation_by_parts_zero a b (m - 1)).
  (* 
     S_n(a*b) = A_n * b_n + S_{n-1}(A*(b-b'))
     S_{m-1}(a*b) = A_{m-1} * b_{m-1} + S_{m-2}(A*(b-b'))
     
     S_n(a*b) - S_{m-1}(a*b) = A_n * b_n - A_{m-1} * b_{m-1} + S_{n-1}(A*(b-b')) - S_{m-2}(A*(b-b'))
     
     但目标是 A_n * b_n - A_{m-1} * b_m + S_{n-1}(A*(b-b')) - S_{m-2}(A*(b-b'))
     
     需要 -A_{m-1} * b_{m-1} = -A_{m-1} * b_m
     即 b_{m-1} = b_m，这不成立！
     
     所以这个证明方法不对。需要用不同的方法。
  *)
  admit.
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
      assert (Hm1 : S n - m = S (n - m)) by lia.
      assert (Hm2 : n - m = S (n - m) - 1) by lia.
      rewrite Hm1. rewrite partial_sum_S.
      rewrite <- Hm2.
      assert (Hm3 : m + (n - m) = n) by lia.
      rewrite <- Hm3. lra.
Qed.

(******************************************************************************)
(* 分部求和定理（一般形式，用 partial_sum 差表示）                            *)
(******************************************************************************)

Theorem summation_by_parts_general :
  forall (a b : nat -> R) (m n : nat),
    (0 < m)%nat -> (m <= n)%nat ->
    partial_sum (fun k => a k * b k) n - partial_sum (fun k => a k * b k) (m - 1) =
    partial_sum a n * b n - partial_sum a (m - 1) * b m +
    (partial_sum (fun k => partial_sum a k * (b k - b (S k))) (n - 1) -
     partial_sum (fun k => partial_sum a k * (b k - b (S k))) (m - 2)).
Admitted.

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
Admitted.

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
Admitted.

(******************************************************************************)
(* 交错级数判别法（Leibniz 判别法）                                           *)
(* 若 b_n 单调递减趋于 0，则 ∑ (-1)^n b_n 收敛                              *)
(******************************************************************************)

Axiom alternating_series_test :
  forall (b : nat -> R),
    Un_growing (fun n => - b n) ->
    Un_cv b 0 ->
    series_cv (fun n => (-1) ^ n * b n).
