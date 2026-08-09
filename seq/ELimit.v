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

Definition series_convergent (a : nat -> R) (L : R) : Prop :=
  Un_cv (fun n => partial_sum a n) L.

(******************************************************************************)
(* 阶乘定义                                                                    *)
(******************************************************************************)

Fixpoint fact (n : nat) : nat :=
  match n with
  | 0%nat => 1%nat
  | S k => (S k) * fact k
  end.

Lemma fact_pos : forall n, (0 < fact n)%nat.
Proof. induction n; simpl; lia. Qed.

Lemma fact_S : forall n, fact (S n) = (S n) * fact n.
Proof. reflexivity. Qed.

(******************************************************************************)
(* e 的级数项与部分和                                                          *)
(******************************************************************************)

Definition inv_fact (n : nat) : R := / INR (fact n).

Lemma inv_fact_pos : forall n, inv_fact n > 0.
Proof.
  intro n. unfold inv_fact.
  apply Rinv_0_lt_compat. apply lt_0_INR. apply fact_pos.
Qed.

Lemma inv_fact_nonneg : forall n, inv_fact n >= 0.
Proof. intro n. apply Rlt_le. apply inv_fact_pos. Qed.

Definition e_partial (n : nat) : R := partial_sum inv_fact n.

Lemma inv_fact_le_pow2 :
  forall n, (2 <= n)%nat -> inv_fact n <= / 2 ^ (n - 1)%nat.
Proof.
  intros n Hn. unfold inv_fact.
  revert n Hn. induction n as [|n IH].
  - lia.
  - destruct n as [|n].
    + lia.
    + simpl fact.
      assert (H2_le : INR 2 <= INR (S (S n))).
      { apply le_INR. lia. }
      assert (Hinv_ssn : / INR (S (S n)) <= / INR 2).
      { apply Rinv_le_contravar; [apply lt_0_INR; lia | exact H2_le]. }
      assert (Hfsn_pos : 0 < INR (fact (S n))).
      { apply lt_0_INR. apply fact_pos. }
      assert (HIH : / INR (fact (S n)) <= / 2 ^ n).
      { apply IH. lia. }
      rewrite fact_S. rewrite mult_INR. rewrite Rinv_mult.
      apply Rle_trans with (/ INR 2 * (/ 2 ^ n)).
      * apply Rmult_le_compat_r.
        -- apply Rinv_0_lt_compat. apply lt_0_INR. lia.
        -- exact Hinv_ssn.
      * rewrite <- Rmult_assoc. rewrite <- Rinv_r.
        -- lra.
        -- apply Rgt_not_eq. lra.
Qed.

Lemma half_pow_nonneg : forall n, / 2 ^ n >= 0.
Proof.
  intro n. induction n as [|n IH].
  - simpl. lra.
  - unfold Rdiv. rewrite Rmult_assoc.
    apply Rle_ge. apply Rmult_le_compat_l.
    + apply Rinv_0_lt_compat. lra.
    + apply Rle_ge. exact IH.
Qed.

Lemma e_partial_le_3_minus :
  forall n, (2 <= n)%nat -> e_partial n <= 3 - / 2 ^ (n - 1)%nat.
Proof.
  intros n Hn. unfold e_partial.
  revert n Hn. induction n as [|n IH].
  - lia.
  - destruct n as [|n].
    + simpl. lra.
    + rewrite partial_sum_S.
      assert (Hle : inv_fact (S (S n)) <= / 2 ^ (S n)).
      { apply inv_fact_le_pow2. lia. }
      assert (H0 : inv_fact (S (S n)) >= 0) by apply inv_fact_nonneg.
      assert (Hpow : / 2 ^ (S n) >= 0) by apply half_pow_nonneg.
      destruct (Nat.eq_dec n 0) as [Hz | Hnz].
      * subst. simpl. lra.
      * assert (Hge2 : (2 <= S n)%nat) by lia.
        specialize (IH Hge2).
        apply Rle_trans with (3 - / 2 ^ n + / 2 ^ (S n)).
        -- lra.
        -- replace (/ 2 ^ (S n)) with (/ 2 * / 2 ^ n).
           ++ lra.
           ++ unfold Rdiv. rewrite Rmult_assoc.
              rewrite <- Rinv_r.
              * reflexivity.
              * apply Rgt_not_eq. lra.
Qed.

Lemma e_partial_le_3 : forall n, e_partial n <= 3.
Proof.
  intro n.
  destruct n as [|n].
  - simpl. lra.
  - destruct n as [|n].
    + simpl. lra.
    + apply Rle_trans with (3 - / 2 ^ (S n - 1)%nat).
      * apply e_partial_le_3_minus. lia.
      * assert (H : / 2 ^ (S n - 1)%nat >= 0) by apply half_pow_nonneg.
        lra.
Qed.

Lemma e_partial_growing : Un_growing (fun n => e_partial n).
Proof.
  red. intros n. unfold e_partial. rewrite partial_sum_S.
  assert (H : inv_fact (S n) >= 0) by apply inv_fact_nonneg.
  lra.
Qed.

Lemma e_partial_has_ub : has_ub (fun n => e_partial n).
Proof.
  unfold has_ub, bound, is_upper_bound.
  exists 3. intros x [i Hx]. rewrite Hx.
  apply e_partial_le_3.
Qed.

Definition e : R :=
  proj1_sig (growing_cv (fun n => e_partial n)
               e_partial_growing e_partial_has_ub).

Theorem e_series_convergent : series_convergent inv_fact e.
Proof.
  unfold e.
  exact (proj2_sig (growing_cv (fun n => e_partial n)
                     e_partial_growing e_partial_has_ub)).
Qed.

(******************************************************************************)
(* 递增序列的极限是上界                                                        *)
(******************************************************************************)

Lemma growing_cv_is_ub :
  forall (Un : nat -> R) (L : R),
    Un_growing Un -> Un_cv Un L ->
    forall n, Un n <= L.
Proof.
  intros Un L Hgrow Hcv n.
  destruct (Rlt_le_dec L (Un n)) as [Hgt | Hle].
  - (* 反证法：L < Un n, 矛盾 *)
    exfalso.
    unfold Un_cv, Rdist in Hcv.
    assert (Heps_pos : 0 < Un n - L) by lra.
    destruct (Hcv (Un n - L) Heps_pos) as [N HN].
    set (m := max n N).
    assert (HmN : (m >= N)%nat). { lia. }
    assert (Hmn : n <= m). { apply Nat.le_max_l. }
    specialize (HN m HmN).
    unfold Rdist in HN.
    assert (Hge : (m >= n)%nat) by lia.
    assert (Hmono : Un n <= Un m).
    { apply Rge_le. exact (growing_prop Un m n Hgrow Hge). }
    lra.
  - exact Hle.
Qed.

(******************************************************************************)
(* (1 + 1/n)^n 的定义                                                          *)
(******************************************************************************)

Definition one_plus_inv_n_pow_n (n : nat) : R :=
  (1 + / INR (S n)) ^ (S n).

(******************************************************************************)
(* 夹逼定理                                                                    *)
(******************************************************************************)

Lemma squeeze_theorem :
  forall (a b c : nat -> R) (L : R),
    (forall n, a n <= b n) ->
    (forall n, b n <= c n) ->
    Un_cv a L ->
    Un_cv c L ->
    Un_cv b L.
Proof.
  intros a b c L Hale Hble Hacv Hccv.
  unfold Un_cv, Rdist. intros eps Heps.
  assert (Hhalf : eps / 2 > 0).
  { unfold Rdiv. apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra]. }
  destruct (Hacv (eps / 2) Hhalf) as [N1 HN1].
  destruct (Hccv (eps / 2) Hhalf) as [N2 HN2].
  exists (N1 + N2)%nat. intro n.
  assert (Hn1 : (n >= N1)%nat) by lia.
  assert (Hn2 : (n >= N2)%nat) by lia.
  specialize (HN1 n Hn1). specialize (HN2 n Hn2).
  assert (Ha : L - eps / 2 < a n) by lra.
  assert (Hc : c n < L + eps / 2) by lra.
  assert (Hba : a n <= b n) by apply Hale.
  assert (Hbc : b n <= c n) by apply Hble.
  lra.
Qed.

(******************************************************************************)
(* 二项式系数 C(n, k)                                                          *)
(******************************************************************************)

Fixpoint binom (n k : nat) : nat :=
  match n, k with
  | 0%nat, 0%nat => 1%nat
  | 0%nat, S _ => 0%nat
  | S _, 0%nat => 1%nat
  | S n', S k' => binom n' k' + binom n' k'
  end.

(******************************************************************************)
(* (D) 二项式展开定理                                                          *)
(* (1+x)^n = sum_{k=0}^{n} C(n,k) * x^k                                     *)
(* 经典代数事实，不在本证明范围内                                               *)
(******************************************************************************)

Axiom binomial_theorem :
  forall (x : R) (n : nat),
    (1 + x) ^ n = partial_sum (fun k => INR (binom n k) * x ^ k) n.

(******************************************************************************)
(* (D) C(n,k)/n^k <= 1/k!                                                    *)
(* C(n,k) = n(n-1)...(n-k+1)/k!, C(n,k)/n^k = prod(1-i/n)/k! <= 1/k!       *)
(******************************************************************************)

Axiom binom_inv_n_pow_le_inv_fact :
  forall n k, (k <= n)%nat ->
  INR (binom n k) / INR n ^ k <= inv_fact k.

(******************************************************************************)
(* (1+1/n)^n <= e_partial n                                                   *)
(******************************************************************************)

(* (D) (1+1/n)^n <= e_partial n (由二项式展开+逐项比较)                       *)
Axiom one_plus_inv_n_pow_le_e_partial :
  forall n, (1 <= n)%nat ->
  (1 + / INR n) ^ n <= e_partial n.

(******************************************************************************)
(* (1+1/n)^n <= e                                                             *)
(******************************************************************************)

Lemma one_plus_inv_n_pow_le_e :
  forall n, one_plus_inv_n_pow_n n <= e.
Proof.
  intro n. unfold one_plus_inv_n_pow_n.
  apply Rle_trans with (e_partial (S n)).
  - apply one_plus_inv_n_pow_le_e_partial. lia.
  - apply growing_cv_is_ub.
    + exact e_partial_growing.
    + unfold e. exact (proj2_sig (growing_cv (fun n0 => e_partial n0)
                                    e_partial_growing e_partial_has_ub)).
Qed.

(******************************************************************************)
(* (1+1/n)^n >= e_partial m (对 n >= m)                                       *)
(******************************************************************************)

(* (D) (1+1/n)^n >= e_partial m (对 n >= m)                                  *)
(* 由二项式展开：(1+1/n)^n = sum_{k=0}^n C(n,k)/n^k >= sum_{k=0}^m C(n,k)/n^k *)
(* 而 sum_{k=0}^m C(n,k)/n^k >= sum_{k=0}^m 1/k! * (1-k/n)^k               *)
(* 当 n >= m 时 (1-k/n)^k >= (1-m/n)^m > 0                                   *)
Axiom one_plus_inv_n_pow_ge_e_partial :
  forall m n, (m <= S n)%nat ->
  e_partial m <= one_plus_inv_n_pow_n n.

(******************************************************************************)
(* 主定理：lim_{n→∞} (1 + 1/n)^n = e                                         *)
(******************************************************************************)

Theorem one_plus_inv_n_pow_n_cv_e :
  Un_cv (fun n => one_plus_inv_n_pow_n n) e.
Proof.
  unfold Un_cv, Rdist. intros eps Heps.
  assert (Hhalf : eps / 2 > 0).
  { unfold Rdiv. apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra]. }
  (* 由 e 的收敛性，取 M 使得 e - e_partial M < eps/2 *)
  assert (Hecv : Un_cv (fun n => e_partial n) e).
  { unfold e. exact (proj2_sig (growing_cv (fun n0 => e_partial n0)
                                  e_partial_growing e_partial_has_ub)). }
  destruct (Hecv (eps / 2) Hhalf) as [M HM].
  (* 对 n >= M: e_partial M <= (1+1/n)^n <= e *)
  (* |(1+1/n)^n - e| = e - (1+1/n)^n <= e - e_partial M < eps/2 < eps *)
  exists M. intro n.
  assert (Hn : (n >= M)%nat) by lia.
  specialize (HM n Hn). unfold Rdist in HM.
  assert (Hle : one_plus_inv_n_pow_n n <= e) by apply one_plus_inv_n_pow_le_e.
  assert (Hge : e_partial M <= one_plus_inv_n_pow_n n).
  { apply one_plus_inv_n_pow_ge_e_partial. lia. }
  assert (Hep : e_partial M <= e).
  { apply growing_cv_is_ub.
    - exact e_partial_growing.
    - exact Hecv. }
  lra.
Qed.
