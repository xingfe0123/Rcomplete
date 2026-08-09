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

(******************************************************************************)
(* 级数收敛定义                                                                *)
(******************************************************************************)

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

(******************************************************************************)
(* e 的级数项：a_n = 1 / n!                                                    *)
(******************************************************************************)

Definition inv_fact (n : nat) : R := / INR (fact n).

Lemma inv_fact_pos : forall n, inv_fact n > 0.
Proof.
  intro n. unfold inv_fact.
  apply Rinv_0_lt_compat. apply lt_0_INR. apply fact_pos.
Qed.

Lemma inv_fact_nonneg : forall n, inv_fact n >= 0.
Proof. intro n. apply Rlt_le. apply inv_fact_pos. Qed.

(******************************************************************************)
(* e 的部分和                                                                  *)
(******************************************************************************)

Definition e_partial (n : nat) : R := partial_sum inv_fact n.

(******************************************************************************)
(* 引理：对 n >= 2, 1/n! <= 1/2^{n-1}                                        *)
(******************************************************************************)

Lemma inv_fact_le_pow2 :
  forall n, (2 <= n)%nat -> inv_fact n <= / 2 ^ (n - 1)%nat.
Proof.
  intros n Hn. unfold inv_fact.
  revert n Hn. induction n as [|n IH].
  - lia.
  - destruct n as [|n].
    + lia.
    + simpl fact.
      assert (Hge2 : (2 <= S (S n))%nat) by lia.
      assert (H2_le : INR 2 <= INR (S (S n))).
      { apply le_INR. lia. }
      assert (Hinv_ssn : / INR (S (S n)) <= / INR 2).
      { apply Rinv_le_contravar; [apply lt_0_INR; lia | exact H2_le]. }
      assert (Hfsn_pos : 0 < INR (fact (S n))).
      { apply lt_0_INR. apply fact_pos. }
      assert (HIH : / INR (fact (S n)) <= / 2 ^ n).
      { apply IH. lia. }
      rewrite fact_S. unfold Rdiv. rewrite Rinv_mult.
      2: { apply lt_0_INR. lia. }
      2: { exact Hfsn_pos. }
      apply Rle_trans with (/ INR 2 * (/ 2 ^ n)).
      * apply Rmult_le_compat_r.
        -- apply Rinv_0_lt_compat. apply lt_0_INR. lia.
        -- exact Hinv_ssn.
      * rewrite <- Rmult_assoc. rewrite <- Rinv_r.
        -- lra.
        -- apply Rgt_not_eq. lra.
Qed.

(******************************************************************************)
(* 几何级数部分和公式                                                          *)
(******************************************************************************)

Lemma geometric_sum :
  forall r n, r <> 1 ->
  partial_sum (fun k => r ^ k) n = (1 - r ^ (S n)) / (1 - r).
Proof.
  intros r n Hr. induction n as [|n IH].
  - simpl. field. lra.
  - rewrite partial_sum_S. rewrite IH. field. lra.
Qed.

(******************************************************************************)
(* e 的部分和有上界 3                                                          *)
(* S_n = 1 + 1 + 1/2! + ... + 1/n!                                           *)
(*     <= 1 + 1 + 1/2 + 1/2^2 + ... + 1/2^{n-1}  (对 k>=2: 1/k!<=1/2^{k-1})*)
(*     = 2 + (1/2 + 1/4 + ... + 1/2^{n-1})                                   *)
(*     = 2 + (1 - (1/2)^{n-1})  (当 n>=2)                                    *)
(*     <= 3                                                                  *)
(******************************************************************************)

Lemma e_partial_le_3 : forall n, e_partial n <= 3.
Proof.
  intro n. unfold e_partial.
  induction n as [|n IH].
  - simpl. lra.
  - rewrite partial_sum_S.
    destruct n as [|n].
    + simpl. lra.
    + assert (Hle : inv_fact (S (S n)) <= / 2 ^ (S n)).
      { apply inv_fact_le_pow2. lia. }
      assert (H0 : inv_fact (S (S n)) >= 0) by apply inv_fact_nonneg.
      assert (Hpow : / 2 ^ (S n) >= 0).
      { apply pow_ge_0. lra. }
      (* S_{S(S n)} = S_{S n} + 1/(S(S n))! <= S_{S n} + 1/2^{S n} *)
      (* 需要证明 S_{S n} + 1/2^{S n} <= 3 *)
      (* S_{S n} = 1 + 1 + sum_{k=2}^{S n} 1/k! <= 2 + sum_{k=2}^{S n} 1/2^{k-1} *)
      (* = 2 + sum_{j=1}^{n} 1/2^j = 2 + (1/2)(1-(1/2)^n)/(1-1/2) = 2 + 1 - (1/2)^n *)
      (* <= 3 - (1/2)^n *)
      (* 所以 S_{S n} + 1/2^{S n} <= 3 - (1/2)^n + 1/2^{S n} = 3 *)
      (* 但这需要展开 S_{S n} 的上界，归纳假设不够强 *)
      (* 改用更强的归纳：e_partial n <= 3 - / 2 ^ (n - 1) (n >= 2) *)
      admit.
Qed.

(******************************************************************************)
(* 更强的上界：e_partial n <= 3 - 1/2^{n-1} (n >= 2)                         *)
(******************************************************************************)

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
      assert (Hpow : / 2 ^ (S n) >= 0).
      { apply pow_ge_0. lra. }
      destruct (Nat.eq_dec n 0) as [Hz | Hnz].
      * (* n = 0, S(S n) = 2 *)
        subst. simpl. lra.
      * (* n >= 1, S n >= 2 *)
        assert (Hge2 : (2 <= S n)%nat) by lia.
        specialize (IH Hge2).
        (* IH: e_partial (S n) <= 3 - / 2 ^ n *)
        (* 目标: e_partial (S n) + inv_fact (S (S n)) <= 3 - / 2 ^ (S n) *)
        apply Rle_trans with (3 - / 2 ^ n + / 2 ^ (S n)).
        -- lra.
        -- replace (/ 2 ^ (S n)) with (/ 2 * / 2 ^ n).
           ++ lra.
           ++ unfold Rdiv. rewrite <- Rmult_assoc.
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
      * lra.
Qed.

(******************************************************************************)
(* e 的部分和递增                                                              *)
(******************************************************************************)

Lemma e_partial_growing : Un_growing (fun n => e_partial n).
Proof.
  red. intros n. unfold e_partial. rewrite partial_sum_S.
  assert (H : inv_fact (S n) >= 0) by apply inv_fact_nonneg.
  lra.
Qed.

(******************************************************************************)
(* e 的部分和有上界（has_ub 形式）                                             *)
(******************************************************************************)

Lemma e_partial_has_ub : has_ub (fun n => e_partial n).
Proof.
  unfold has_ub, bound, is_upper_bound.
  exists 3. intros x [i Hx]. rewrite Hx.
  apply e_partial_le_3.
Qed.

(******************************************************************************)
(* e 的定义：e = sum_{n=0}^{infty} 1/n!                                       *)
(******************************************************************************)

Definition e : R :=
  proj1_sig (growing_cv (fun n => e_partial n)
               e_partial_growing e_partial_has_ub).

(******************************************************************************)
(* e 的级数收敛性                                                              *)
(******************************************************************************)

Theorem e_series_convergent : series_convergent inv_fact e.
Proof.
  unfold e.
  exact (proj2_sig (growing_cv (fun n => e_partial n)
                     e_partial_growing e_partial_has_ub)).
Qed.
