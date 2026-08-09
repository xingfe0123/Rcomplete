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
  intros c a b [A HA] [B HB].
  destruct (series_plus_cv a b) as [AB HAB].
  destruct (series_plus_cv (fun n => c * a n) (fun n => c * b n)
    (series_scal_cv c a) (series_scal_cv c b)) as [AB2 HAB2].
  simpl. lra.
Qed.
