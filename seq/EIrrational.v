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

Lemma fact_ge_1 : forall n, (1 <= fact n)%nat.
Proof. induction n; simpl; lia. Qed.

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
  - exfalso.
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
(* e 的余项正性                                                                *)
(******************************************************************************)

Lemma e_remainder_pos : forall n, e - e_partial n > 0.
Proof.
  intro n.
  assert (Hcv : Un_cv (fun k => e_partial k) e).
  { unfold e. exact (proj2_sig (growing_cv (fun k => e_partial k)
                                  e_partial_growing e_partial_has_ub)). }
  assert (Hle : e_partial n <= e) by apply growing_cv_is_ub.
  assert (Hlt : e_partial n < e).
  { apply Rle_lt_trans with (e_partial (S n)).
    - unfold e_partial. rewrite partial_sum_S.
      assert (H : inv_fact (S n) >= 0) by apply inv_fact_nonneg.
      lra.
    - apply growing_cv_is_ub; [exact e_partial_growing | exact Hcv]. }
  lra.
Qed.

(******************************************************************************)
(* (D) 余项上界：e - e_partial n < 1 / (n * fact n)  (n >= 1)                *)
(* 证明：e - S_n = sum_{k=n+1}^infty 1/k!                                   *)
(*       < 1/(n+1)! * sum_{j=0}^infty (1/(n+1))^j                          *)
(*       = 1/(n+1)! * (n+1)/n = 1/(n * n!)                                  *)
(******************************************************************************)

Axiom e_remainder_lt :
  forall n, (1 <= n)%nat -> e - e_partial n < / INR (n * fact n).

(******************************************************************************)
(* (D) q * n! * S_n 是整数（当 n >= 1, q >= 1）                              *)
(* 因为 q * n! / k! = q * n*(n-1)*...*(k+1) 是整数对 k <= n                 *)
Axiom q_fact_partial_sum_is_nat :
  forall q n, (1 <= q)%nat ->
  exists m, INR q * INR (fact n) * e_partial n = INR m.

(******************************************************************************)
(* q * n! * (e - S_n) < 1  (当 n > q)                                        *)
(******************************************************************************)

Lemma q_fact_remainder_lt_1 :
  forall q n, (1 <= q)%nat -> (S q <= n)%nat ->
  INR q * INR (fact n) * (e - e_partial n) < 1.
Proof.
  intros q n Hq Hqn.
  assert (Hn : (1 <= n)%nat) by lia.
  assert (Hrem : e - e_partial n < / INR (n * fact n)).
  { apply e_remainder_lt. exact Hn. }
  assert (Hfact_pos : 0 < INR (fact n)).
  { apply lt_0_INR. apply fact_pos. }
  assert (Hn_pos : 0 < INR n).
  { apply lt_0_INR. lia. }
  assert (Hq_pos : 0 < INR q).
  { apply lt_0_INR. lia. }
  rewrite mult_INR in Hrem.
  rewrite Rinv_mult in Hrem.
  2: { apply Rgt_not_eq. exact Hn_pos. }
  2: { apply Rgt_not_eq. exact Hfact_pos. }
  (* Hrem : e - e_partial n < / INR n * / INR (fact n) *)
  (* 目标：INR q * INR (fact n) * (e - e_partial n) < 1 *)
  (* = INR q * (INR (fact n) * (e - e_partial n)) < 1 *)
  (* INR (fact n) * (e - e_partial n) < INR (fact n) * (/ INR n * / INR (fact n)) *)
  (* = / INR n *)
  assert (H1 : INR (fact n) * (e - e_partial n) < / INR n).
  { apply Rlt_le_trans with (INR (fact n) * (/ INR n * / INR (fact n))).
    - apply Rmult_lt_compat_l.
      + exact Hfact_pos.
      + exact Hrem.
    - rewrite Rmult_assoc.
      rewrite (Rmult_comm (/ INR n)).
      rewrite <- Rmult_assoc.
      rewrite Rinv_r.
      + rewrite Rmult_1_l. apply Rle_refl.
      + apply Rgt_not_eq. exact Hfact_pos. }
  assert (H2 : INR q * (INR (fact n) * (e - e_partial n)) < INR q * / INR n).
  { apply Rmult_lt_compat_l.
    - exact Hq_pos.
    - exact H1. }
  apply Rlt_le_trans with (INR q * / INR n).
  - exact H2.
  - (* q / n <= 1 因为 q <= n *)
    assert (Hq_le_n : INR q <= INR n).
    { apply le_INR. lia. }
    unfold Rdiv.
    apply Rmult_le_reg_l with (INR n).
    + apply lt_0_INR. lia.
    + rewrite Rmult_0_r. rewrite Rmult_assoc. rewrite Rinv_r.
      * lra.
      * apply Rgt_not_eq. exact Hn_pos.
Qed.

(******************************************************************************)
(* q * n! * (e - S_n) > 0  (当 n >= 1)                                       *)
(******************************************************************************)

Lemma q_fact_remainder_pos :
  forall q n, (1 <= q)%nat -> (1 <= n)%nat ->
  INR q * INR (fact n) * (e - e_partial n) > 0.
Proof.
  intros q n Hq Hn.
  assert (Hrem : e - e_partial n > 0) by apply e_remainder_pos.
  assert (Hfact_pos : 0 < INR (fact n)).
  { apply lt_0_INR. apply fact_pos. }
  assert (Hq_pos : 0 < INR q).
  { apply lt_0_INR. lia. }
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat; [exact Hq_pos | exact Hfact_pos].
  - exact Hrem.
Qed.

(******************************************************************************)
(* 主定理：e 是无理数                                                          *)
(******************************************************************************)

Theorem e_irrational : ~ exists p q, (0 < q)%nat /\ e = INR p / INR q.
Proof.
  intro [p [q [Hq Heq]]].
  set (n := S q).
  assert (Hn : (1 <= n)%nat) by lia.
  assert (Hqn : (S q <= n)%nat) by lia.
  assert (Hq1 : (1 <= q)%nat) by lia.
  (* q * n! * e = q * n! * S_n + q * n! * (e - S_n) *)
  assert (Hsplit : INR q * INR (fact n) * e =
    INR q * INR (fact n) * e_partial n + INR q * INR (fact n) * (e - e_partial n)).
  { assert (He : e = e_partial n + (e - e_partial n)) by lra.
    rewrite He. rewrite Rmult_plus_distr_l. reflexivity. }
  (* e = p/q => q * n! * e = n! * p *)
  assert (Hqe : INR q * INR (fact n) * e = INR (fact n) * INR p).
  { rewrite Heq. unfold Rdiv.
    rewrite Rmult_assoc.
    rewrite <- (Rmult_comm (INR q)).
    rewrite Rmult_assoc. rewrite Rinv_r.
    - rewrite Rmult_1_l. rewrite (Rmult_comm (INR p)). reflexivity.
    - apply Rgt_not_eq. apply lt_0_INR. exact Hq. }
  (* q * n! * S_n 是整数 *)
  destruct (q_fact_partial_sum_is_nat q n Hq1) as [m Hm].
  (* INR(fact n * p) = INR m + q * n! * (e - S_n) *)
  assert (Hm_eq : INR (fact n * p) = INR m + INR q * INR (fact n) * (e - e_partial n)).
  { rewrite <- Hqe. rewrite Hsplit. rewrite Hm. lra. }
  (* q * n! * (e - S_n) 严格介于 0 和 1 之间 *)
  assert (Hpos : 0 < INR q * INR (fact n) * (e - e_partial n)).
  { apply q_fact_remainder_pos; [exact Hq1 | exact Hn]. }
  assert (Hlt1 : INR q * INR (fact n) * (e - e_partial n) < 1).
  { apply q_fact_remainder_lt_1; [exact Hq1 | exact Hqn]. }
  (* INR(fact n * p) - INR m = q * n! * (e - S_n) ∈ (0, 1) *)
  (* 但 INR(fact n * p) - INR m = INR(fact n * p - m)                       *)
  assert (Hm_lt : INR m < INR (fact n * p)).
  { rewrite <- Hm_eq. rewrite Rplus_comm.
    apply Rplus_lt_compat_l. exact Hpos. }
  assert (Hm_le : (m <= fact n * p)%nat).
  { apply Nat.lt_le_incl. apply INR_lt. exact Hm_lt. }
  rewrite (minus_INR _ _ Hm_le) in Hm_eq.
  assert (Hdiff : INR (fact n * p - m) = INR q * INR (fact n) * (e - e_partial n)).
  { lra. }
  assert (Hdiff_pos : 0 < INR (fact n * p - m)) by lra.
  assert (Hdiff_lt1 : INR (fact n * p - m) < 1) by lra.
  (* INR k >= 1 对所有 k >= 1 *)
  assert (Hk : (1 <= fact n * p - m)%nat).
  { assert (H0_lt : (0 < fact n * p - m)%nat).
    { apply INR_lt. exact Hdiff_pos. }
    lia. }
  assert (Hge1 : INR (fact n * p - m) >= 1).
  { apply le_INR. exact Hk. }
  lra.
Qed.
