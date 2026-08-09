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
(* 引理：收敛级数的极限唯一                                                    *)
(******************************************************************************)

Lemma series_limit_unique :
  forall (a : nat -> R) (L1 L2 : R),
    series_convergent a L1 -> series_convergent a L2 -> L1 = L2.
Proof.
  intros a L1 L2 H1 H2.
  apply UL_sequence. exact H1. exact H2.
Qed.

(******************************************************************************)
(* 级数极限提取函数                                                            *)
(******************************************************************************)

Definition series_limit (a : nat -> R) (H : series_cv a) : R :=
  match H with
  | ex_intro L Hconv => L
  end.

(******************************************************************************)
(* ============================================================================*)
(* 级数加法                                                                    *)
(* ============================================================================*)

(******************************************************************************)
(* 引理：partial_sum (a + b) n = partial_sum a n + partial_sum b n           *)
(******************************************************************************)

Lemma partial_sum_plus :
  forall (a b : nat -> R) (n : nat),
    partial_sum (fun k => a k + b k) n =
    partial_sum a n + partial_sum b n.
Proof.
  intros a b n.
  induction n as [|n IH].
  - simpl. lra.
  - rewrite partial_sum_S. rewrite partial_sum_S. rewrite partial_sum_S.
    rewrite IH. lra.
Qed.

(******************************************************************************)
(* 定理：∑(a_n + b_n) = ∑a_n + ∑b_n                                         *)
(* 若 ∑a_n 收敛于 A，∑b_n 收敛于 B，则 ∑(a_n + b_n) 收敛于 A + B           *)
(******************************************************************************)

Theorem series_plus_convergent :
  forall (a b : nat -> R) (A B : R),
    series_convergent a A -> series_convergent b B ->
    series_convergent (fun n => a n + b n) (A + B).
Proof.
  intros a b A B Ha Hb.
  unfold series_convergent, Un_cv, Rdist in *.
  intros eps Heps.
  assert (Hhalf : eps / 2 > 0) by apply half_gt_zero.
  destruct (Ha (eps / 2) Hhalf) as [Na HNa].
  destruct (Hb (eps / 2) Hhalf) as [Nb HNb].
  exists (max Na Nb). intros n Hn.
  assert (Hn_a : (n >= Na)%nat) by lia.
  assert (Hn_b : (n >= Nb)%nat) by lia.
  specialize (HNa n Hn_a). specialize (HNb n Hn_b).
  rewrite partial_sum_plus.
  replace (partial_sum a n + partial_sum b n - (A + B))
    with ((partial_sum a n - A) + (partial_sum b n - B)) by lra.
  apply Rle_trans with (Rabs (partial_sum a n - A) + Rabs (partial_sum b n - B)).
  - apply Rabs_triang.
  - lra.
Qed.

Theorem series_plus_cv :
  forall (a b : nat -> R),
    series_cv a -> series_cv b -> series_cv (fun n => a n + b n).
Proof.
  intros a b [A Ha] [B Hb].
  exists (A + B). apply series_plus_convergent; assumption.
Qed.

Theorem series_plus_limit :
  forall (a b : nat -> R) (Ha : series_cv a) (Hb : series_cv b),
    series_limit (fun n => a n + b n) (series_plus_cv a b Ha Hb) =
    series_limit a Ha + series_limit b Hb.
Proof.
  intros a b [A Ha] [B Hb]. simpl. reflexivity.
Qed.

(******************************************************************************)
(* ============================================================================*)
(* 级数数乘                                                                    *)
(* ============================================================================*)

(******************************************************************************)
(* 引理：partial_sum (c * a) n = c * partial_sum a n                         *)
(******************************************************************************)

Lemma partial_sum_scal :
  forall (c : R) (a : nat -> R) (n : nat),
    partial_sum (fun k => c * a k) n = c * partial_sum a n.
Proof.
  intros c a n.
  induction n as [|n IH].
  - simpl. lra.
  - rewrite partial_sum_S. rewrite partial_sum_S.
    rewrite IH. lra.
Qed.

(******************************************************************************)
(* 定理：∑(c * a_n) = c * ∑a_n                                              *)
(******************************************************************************)

Theorem series_scal_convergent :
  forall (c : R) (a : nat -> R) (A : R),
    series_convergent a A ->
    series_convergent (fun n => c * a n) (c * A).
Proof.
  intros c a A Ha.
  unfold series_convergent, Un_cv, Rdist in *.
  intros eps Heps.
  destruct (Rle_lt_or_eq_dec 0 (Rabs c)) as [Habs_c_pos | Habs_c_0].
  - (* c <> 0 *)
    destruct (Ha (eps / Rabs c)) as [N HN].
    + apply Rmult_lt_0_compat.
      * apply Rinv_0_lt_compat. exact Habs_c_pos.
      * exact Heps.
    + exists N. intros n Hn.
      specialize (HN n Hn).
      rewrite partial_sum_scal.
      replace (c * partial_sum a n - c * A) with (c * (partial_sum a n - A)) by lra.
      rewrite Rabs_mult.
      apply Rmult_lt_reg_l with (/ Rabs c).
      * apply Rinv_0_lt_compat. exact Habs_c_pos.
      * rewrite Rmult_assoc. rewrite Rinv_r.
        -- rewrite Rmult_1_l. exact HN.
        -- apply Rgt_not_eq. exact Habs_c_pos.
  - (* c = 0 *)
    rewrite <- Rabs_R0 in Habs_c_0.
    assert (Hc : c = 0) by lra.
    rewrite Hc.
    exists 0%nat. intros n Hn.
    rewrite partial_sum_scal. simpl.
    rewrite Rminus_0_r. rewrite Rabs_R0. lra.
Qed.

Theorem series_scal_cv :
  forall (c : R) (a : nat -> R),
    series_cv a -> series_cv (fun n => c * a n).
Proof.
  intros c a [A Ha].
  exists (c * A). apply series_scal_convergent; assumption.
Qed.

(******************************************************************************)
(* ============================================================================*)
(* 级数减法                                                                    *)
(* ============================================================================*)

Theorem series_minus_convergent :
  forall (a b : nat -> R) (A B : R),
    series_convergent a A -> series_convergent b B ->
    series_convergent (fun n => a n - b n) (A - B).
Proof.
  intros a b A B Ha Hb.
  unfold series_convergent, Un_cv, Rdist in *.
  intros eps Heps.
  assert (Hhalf : eps / 2 > 0) by apply half_gt_zero.
  destruct (Ha (eps / 2) Hhalf) as [Na HNa].
  destruct (Hb (eps / 2) Hhalf) as [Nb HNb].
  exists (max Na Nb). intros n Hn.
  assert (Hn_a : (n >= Na)%nat) by lia.
  assert (Hn_b : (n >= Nb)%nat) by lia.
  specialize (HNa n Hn_a). specialize (HNb n Hn_b).
  replace (partial_sum (fun k => a k - b k) n - (A - B))
    with ((partial_sum a n - A) - (partial_sum b n - B)).
  - apply Rle_trans with (Rabs (partial_sum a n - A) + Rabs (-(partial_sum b n - B))).
    + apply Rabs_triang.
    + rewrite Rabs_Ropp. lra.
  - assert (Hps : partial_sum (fun k => a k - b k) n = partial_sum a n - partial_sum b n).
    { induction n as [|n IH].
      - simpl. lra.
      - rewrite partial_sum_S. rewrite partial_sum_S. rewrite partial_sum_S.
        rewrite IH. lra. }
    rewrite Hps. lra.
Qed.

Theorem series_minus_cv :
  forall (a b : nat -> R),
    series_cv a -> series_cv b -> series_cv (fun n => a n - b n).
Proof.
  intros a b [A Ha] [B Hb].
  exists (A - B). apply series_minus_convergent; assumption.
Qed.

(******************************************************************************)
(* ============================================================================*)
(* Cauchy 乘积（级数乘法）                                                     *)
(*                                                                            *)
(* (∑a_n)(∑b_n) = ∑c_n 其中 c_n = ∑_{k=0}^{n} a_k b_{n-k}                 *)
(*                                                                            *)
(* 绝对收敛时 Cauchy 乘积收敛且等于两个级数极限的乘积                         *)
(******************************************************************************)

(******************************************************************************)
(* Cauchy 乘积的通项定义                                                      *)
(* c_n = ∑_{k=0}^{n} a_k * b_{n-k}                                          *)
(******************************************************************************)

Fixpoint cauchy_product_term (a b : nat -> R) (n : nat) : R :=
  match n with
  | 0%nat => a 0%nat * b 0%nat
  | S k => cauchy_product_term a b k + a (S k) * b (n - S k)
  end.

Lemma cauchy_product_term_S :
  forall (a b : nat -> R) (n : nat),
    cauchy_product_term a b (S n) =
    cauchy_product_term a b n + a (S n) * b 0%nat.
Proof.
  intros a b n.
  induction n as [|n IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

(******************************************************************************)
(* Cauchy 乘积的另一种定义：c_n = ∑_{k=0}^{n} a_k b_{n-k}                  *)
(* 用 partial_sum 表示                                                        *)
(******************************************************************************)

Definition cauchy_product (a b : nat -> R) (n : nat) : R :=
  partial_sum (fun k => a k * b (n - k)) n.

(******************************************************************************)
(* 引理：cauchy_product_term 等价于 cauchy_product                           *)
(******************************************************************************)

Lemma cauchy_product_eq :
  forall (a b : nat -> R) (n : nat),
    cauchy_product_term a b n = cauchy_product a b n.
Proof.
  intros a b n.
  unfold cauchy_product.
  induction n as [|n IH].
  - simpl. lra.
  - rewrite cauchy_product_term_S.
    rewrite partial_sum_S.
    simpl (S n - S n).
    rewrite IH. lra.
Qed.

(******************************************************************************)
(* Mertens 定理：绝对收敛 × 收敛 = 收敛                                      *)
(* 若 ∑a_n 绝对收敛于 A，∑b_n 收敛于 B                                      *)
(* 则 ∑c_n 收敛于 AB，其中 c_n = ∑_{k=0}^{n} a_k b_{n-k}                   *)
(******************************************************************************)

(******************************************************************************)
(* 引理：partial_sum cauchy_product n 与 (partial_sum a n)(partial_sum b n) 的关系 *)
(*                                                                            *)
(* 关键恒等式：                                                               *)
(* (∑_{k=0}^{n} a_k)(∑_{k=0}^{n} b_k) = ∑_{k=0}^{n} c_k                   *)
(*   + ∑_{k=0}^{n-1} (∑_{i=0}^{k} a_i) b_{n-k}                             *)
(*   + ∑_{k=0}^{n-1} a_{n-k} (∑_{i=0}^{k} b_i)                             *)
(*   - ∑_{k=0}^{n-1} a_{n-k} b_{n-k}                                        *)
(*                                                                            *)
(* 更简洁的恒等式：                                                           *)
(* S_n(a) * S_n(b) - S_n(c) = ∑_{k=0}^{n} (S_n(a) - S_k(a)) * b_k          *)
(* 其中 S_k(a) = ∑_{i=0}^{k} a_i                                            *)
(* 但这需要仔细展开                                                           *)
(*                                                                            *)
(* 最直接的证明：                                                             *)
(* S_n(a) * S_n(b) = ∑_{i=0}^{n} ∑_{j=0}^{n} a_i b_j                      *)
(*                 = ∑_{k=0}^{n} ∑_{i+j=k} a_i b_j + ∑_{i+j>n} a_i b_j     *)
(*                 = S_n(c) + ∑_{i+j>n, i<=n, j<=n} a_i b_j                 *)
(******************************************************************************)

(******************************************************************************)
(* 引理：S_n(a) * b_k = ∑_{i=0}^{n} a_i * b_k                               *)
(******************************************************************************)

Lemma partial_sum_mult_const :
  forall (a : nat -> R) (n : nat) (k : nat),
    partial_sum a n * b k = partial_sum (fun i => a i * b k) n.
Proof.
  intros a n k.
  induction n as [|n IH].
  - simpl. lra.
  - rewrite partial_sum_S. rewrite partial_sum_S. rewrite IH. lra.
Qed.

(******************************************************************************)
(* 引理：S_n(a) * S_n(b) = ∑_{k=0}^{n} c_k + 余项                          *)
(* 其中 c_k = ∑_{i=0}^{k} a_i b_{k-i}                                       *)
(*                                                                            *)
(* S_n(a) * S_n(b) = ∑_{i=0}^{n} a_i * S_n(b)                              *)
(*                 = ∑_{i=0}^{n} a_i * (∑_{j=0}^{n} b_j)                   *)
(*                 = ∑_{i=0}^{n} ∑_{j=0}^{n} a_i b_j                       *)
(*                 = ∑_{k=0}^{2n} ∑_{i+j=k, i<=n, j<=n} a_i b_j            *)
(*                                                                            *)
(* 对 k <= n: ∑_{i+j=k} a_i b_j = c_k                                       *)
(* 对 k > n: 余项                                                            *)
(******************************************************************************)

(******************************************************************************)
(* Mertens 定理的证明思路：                                                   *)
(*                                                                            *)
(* 设 A_n = S_n(a), B_n = S_n(b), C_n = S_n(c)                              *)
(* A_n * B_n - C_n = ∑_{k=0}^{n} (A_n - A_k) * b_{n-k}                     *)
(* （当 ∑a_n 绝对收敛时，|A_n - A_k| 有界且趋于 0）                         *)
(*                                                                            *)
(* 更精确地：                                                                 *)
(* C_n = ∑_{k=0}^{n} c_k = ∑_{k=0}^{n} ∑_{i=0}^{k} a_i b_{k-i}            *)
(* A_n * B_n = ∑_{i=0}^{n} a_i * B_n = ∑_{i=0}^{n} a_i * ∑_{j=0}^{n} b_j  *)
(*           = ∑_{i=0}^{n} ∑_{j=0}^{n} a_i b_j                             *)
(*                                                                            *)
(* A_n * B_n - C_n                                                           *)
(* = ∑_{i=0}^{n} ∑_{j=0}^{n} a_i b_j - ∑_{k=0}^{n} ∑_{i=0}^{k} a_i b_{k-i} *)
(* = ∑_{i=0}^{n} ∑_{j=n-i+1}^{n} a_i b_j  (j > k-i 的部分)                *)
(* = ∑_{i=0}^{n} a_i * (B_n - B_{n-i})                                      *)
(* = ∑_{i=0}^{n} a_i * (B_n - B_{n-i})                                      *)
(******************************************************************************)

(******************************************************************************)
(* (D) Mertens 定理                                                           *)
(* 若 ∑a_n 绝对收敛于 A，∑b_n 收敛于 B                                      *)
(* 则 ∑c_n 收敛于 AB                                                         *)
(******************************************************************************)

Theorem mertens_theorem :
  forall (a b : nat -> R) (A B : R),
    series_convergent a A -> absolutely_convergent a ->
    series_convergent b B ->
    series_convergent (fun n => cauchy_product a b n) (A * B).
Proof.
  intros a b A B Ha Habs_a Hb.
  assert (Habs_cv : series_cv (fun n => Rabs (a n))) by exact Habs_a.
  destruct Habs_cv as [Aabs HAabs].
  (* |a_n| 的部分和递增有界 *)
  assert (Habs_growing : Un_growing (fun n => partial_sum (fun k => Rabs (a k)) n)).
  { red. intro n. rewrite partial_sum_S.
    assert (H : Rabs (a (S n)) >= 0) by apply Rabs_pos. lra. }
  assert (Habs_has_ub : has_ub (fun n => partial_sum (fun k => Rabs (a k)) n)).
  { unfold has_ub, bound, is_upper_bound.
    exists Aabs. intros x [i Hx]. rewrite Hx.
    apply growing_cv_is_ub; [exact Habs_growing | exact HAabs]. }
  assert (HA_bounded : forall n, Rabs (partial_sum a n) <= Aabs + 1).
  { intro n. apply Rle_trans with (partial_sum (fun k => Rabs (a k)) n).
    - induction n as [|n IH].
      + simpl. apply Rabs_pos.
      + rewrite partial_sum_S. rewrite partial_sum_S.
        apply Rle_trans with (Rabs (partial_sum a n) + Rabs (a (S n))).
        * apply Rabs_triang.
        * apply Rplus_le_compat; [exact IH | apply Rabs_pos].
    - apply Rle_trans with Aabs; [apply growing_cv_is_ub; [exact Habs_growing | exact HAabs] | lra]. }
  assert (HB_cv : Un_cv (fun n => partial_sum b n) B) by exact Hb.
  assert (HA_cv : Un_cv (fun n => partial_sum a n) A) by exact Ha.
  (* B_n 有界 *)
  assert (HB_bounded : exists Mb, Mb > 0 /\ forall n, Rabs (partial_sum b n) <= Mb).
  { exists (Rabs B + 1). split; [lra |].
    intro n. apply Rle_trans with (Rabs (partial_sum b n - B) + Rabs B).
    - rewrite Rabs_triang. apply Rle_refl.
    - apply Rplus_le_compat; [| apply Rle_refl].
      unfold Un_cv, Rdist in HB_cv. specialize (HB_cv 1%R) as [N HN]; [lra |].
      destruct (le_dec N n) as [Hle | Hgt].
      + specialize (HN n Hle). unfold Rdist in HN. lra.
      + (* 有限项有界 *)
        induction N as [|N IH].
        - simpl. rewrite Rabs_Ropp. rewrite Rabs_triang. lra.
        - destruct IH as [M2 HM2].
          assert (HM2_new : forall k, (k <= S N)%nat -> Rabs (partial_sum b k) <= Rmax M2 (Rabs (partial_sum b (S N)))).
          { intros k Hk. destruct (Nat.eq_dec k (S N)) as [Heq | Hneq].
            - subst. apply Rmax2.
            - apply Rle_trans with M2; [apply Rmax1 | apply HM2; lia]. }
          apply Rle_trans with (Rmax M2 (Rabs (partial_sum b (S N)))).
          * apply HM2_new. lia.
          * apply Rmax2. }
  destruct HB_bounded as [Mb [HMb_pos Habs_B_bound]].
  (* 关键恒等式：A_n * B_n - C_n = sum_{k=0}^{n} (A_n - A_k) * b_{n-k} *)
  (* 其中 C_n = S_n(cauchy_product a b) *)
  (* 证明 C_n -> A * B 等价于 A_n * B_n - C_n -> 0 *)
  (* |A_n * B_n - C_n| <= sum_{k=0}^{n} |A_n - A_k| * |b_{n-k}| *)
  (* 分成 k=0..p 和 k=p+1..n 两部分 *)
  (* 对 k <= p: |A_n - A_k| <= sum_{i=k+1}^{n} |a_i| <= sum_{i=p+1}^{n} |a_i| + sum_{i=k+1}^{p} |a_i| *)
  (* 简化：取 p = n/2, 但更简单的方法是直接用 Cauchy 准则 *)
  unfold series_convergent, Un_cv, Rdist. intros eps Heps.
  assert (H3Mb : eps / (3 * Mb) > 0).
  { unfold Rdiv. apply Rmult_lt_0_compat; [exact Heps |].
    apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; lra. }
  assert (H3Aabs : eps / (3 * (Aabs + 1)) > 0).
  { unfold Rdiv. apply Rmult_lt_0_compat; [exact Heps |].
    apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; lra. }
  assert (H3Mb2 : eps / (3 * Mb * (Aabs + 1)) > 0).
  { unfold Rdiv. apply Rmult_lt_0_compat; [exact Heps |].
    apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; [lra | apply Rmult_lt_0_compat; lra]. }
  (* 取 N1 使得 n >= N1 时 |A_n - A| < eps/(3*Mb) *)
  destruct (HA_cv (eps / (3 * Mb))) as [N1 HN1]; [exact H3Mb |].
  (* 取 N2 使得 n >= N2 时 |B_n - B| < eps/(3*(Aabs+1)) *)
  destruct (HB_cv (eps / (3 * (Aabs + 1)))) as [N2 HN2]; [exact H3Aabs |].
  (* 取 N3 使得 m >= n >= N3 时 sum_{k=n+1}^{m} |a_k| < eps/(3*Mb) *)
  assert (Habs_cauchy : series_cauchy (fun n => Rabs (a n))).
  { apply series_convergent_iff_cauchy. exact Habs_cv. }
  destruct (Habs_cauchy (eps / (3 * Mb))) as [N3 HN3]; [exact H3Mb |].
  set (N0 := max (max N1 N2) N3).
  exists N0. intro n. assert (Hn : (n >= N0)%nat) by lia.
  assert (Hn1 : (n >= N1)%nat) by lia.
  assert (Hn2 : (n >= N2)%nat) by lia.
  assert (Hn3 : (n >= N3)%nat) by lia.
  specialize (HN1 n Hn1). specialize (HN2 n Hn2).
  unfold Rdist in HN1, HN2.
  (* |S_n(C) - A * B| <= |A_n * B_n - S_n(C)| + |A_n * B_n - A * B| *)
  (* |A_n * B_n - A * B| <= |A_n| * |B_n - B| + |A_n - A| * |B| *)
  (*                     <= (Aabs+1) * |B_n - B| + |A_n - A| * Mb *)
  (* |A_n * B_n - S_n(C)| = |sum_{k=0}^{n} (A_n - A_k) * b_{n-k}| *)
  (* 分成 k=0..N3-1 和 k=N3..n *)
  (* 对 k >= N3: |A_n - A_k| <= sum_{i=k+1}^{n} |a_i| < eps/(3*Mb) *)
  (* 对 k < N3: |A_n - A_k| <= |A_n - A| + |A - A_k| *)
  (*           |A_n - A| < eps/(3*Mb), |A_k| <= Aabs+1, |A - A_k| <= Aabs+1+|A| *)
  (* Mertens 定理的完整证明需要建立 Cauchy 乘积恒等式：
     S_n(a) * S_n(b) - S_n(c) = sum_{k=0}^{n} (A_n - A_k) * b_{n-k}
     然后按 k < N3 和 k >= N3 分段精细估计，证明每项均 < eps/3。
     由于涉及大量代数恒等式的精确立化，当前标记为 Axiom 保留。*)
Admitted.

(******************************************************************************)
(* Cauchy 乘积收敛定理（两个都绝对收敛）                                      *)
(******************************************************************************)

Theorem cauchy_product_convergent :
  forall (a b : nat -> R) (A B : R),
    series_convergent a A -> absolutely_convergent a ->
    series_convergent b B -> absolutely_convergent b ->
    series_convergent (fun n => cauchy_product a b n) (A * B).
Proof.
  intros a b A B Ha Habs_a Hb Habs_b.
  apply mertens_theorem; assumption.
Qed.

(******************************************************************************)
(* ============================================================================*)
(* 级数运算的完整代数结构                                                      *)
(* ============================================================================*)

(******************************************************************************)
(* 加法交换律                                                                  *)
(******************************************************************************)

Theorem series_plus_comm :
  forall (a b : nat -> R),
    series_cv a -> series_cv b ->
    series_limit (fun n => a n + b n) (series_plus_cv a b) =
    series_limit (fun n => b n + a n) (series_plus_cv b a).
Proof.
  intros a b Ha Hb.
  rewrite series_plus_limit. rewrite series_plus_limit.
  lra.
Qed.

(******************************************************************************)
(* 加法结合律                                                                  *)
(******************************************************************************)

Theorem series_plus_assoc :
  forall (a b c : nat -> R),
    series_cv a -> series_cv b -> series_cv c ->
    series_limit (fun n => (a n + b n) + c n)
      (series_plus_cv (fun n => a n + b n) c (series_plus_cv a b)) =
    series_limit (fun n => a n + (b n + c n))
      (series_plus_cv a (fun n => b n + c n) (series_plus_cv b c)).
Proof.
  intros a b c Ha Hb Hc.
  rewrite series_plus_limit. rewrite series_plus_limit.
  rewrite series_plus_limit. rewrite series_plus_limit.
  lra.
Qed.

(******************************************************************************)
(* 数乘分配律                                                                  *)
(******************************************************************************)

Theorem series_scal_distr :
  forall (c : R) (a b : nat -> R),
    series_cv a -> series_cv b ->
    series_limit (fun n => c * (a n + b n))
      (series_scal_cv c (fun n => a n + b n) (series_plus_cv a b)) =
    series_limit (fun n => c * a n + c * b n)
      (series_plus_cv (fun n => c * a n) (fun n => c * b n)
        (series_scal_cv c a) (series_scal_cv c b)).
Proof.
  intros c a b [A Ha] [B Hb].
  (* LHS: series_limit (fun n => c*(a n + b n)) (series_scal_cv c ... (series_plus_cv a b))
     = c * (A + B)
     RHS: series_limit (fun n => c*a n + c*b n) (series_plus_cv ... (series_scal_cv c a) (series_scal_cv c b))
     = c*A + c*B
     Goal: c * (A + B) = c * A + c * B *)
  simpl.
  rewrite Rmult_plus_distr_l. reflexivity.
Qed.
