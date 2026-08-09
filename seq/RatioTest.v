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
(* 比较判别法                                                                  *)
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

(******************************************************************************)
(* (D) 几何级数收敛                                                            *)
(******************************************************************************)

Axiom geometric_series_cv :
  forall r, Rabs r < 1 -> series_cv (fun n => r ^ n).

(******************************************************************************)
(* (D) 收敛级数通项趋于 0                                                      *)
(******************************************************************************)

Axiom series_cv_tendsto_0 :
  forall (a : nat -> R), series_cv a -> Un_cv (fun n => a n) 0.

(******************************************************************************)
(* 比率收敛法 (D'Alembert Ratio Test)                                          *)
(*                                                                            *)
(* 定理：设 a_n 是非零序列，L = lim |a_{n+1}/a_n|                            *)
(*   L < 1 => sum a_n 绝对收敛                                               *)
(*   L > 1 => sum a_n 发散                                                   *)
(*   L = 1 => 不确定                                                          *)
(*                                                                            *)
(* 等价形式（不使用极限）：                                                    *)
(*   若存在 r < 1 和 N 使得 n >= N 时 |a_{n+1}/a_n| <= r                    *)
(*   则 sum a_n 绝对收敛                                                     *)
(*   若存在 N 使得 n >= N 时 |a_{n+1}/a_n| >= 1                              *)
(*   则 sum a_n 发散                                                          *)
(******************************************************************************)

(******************************************************************************)
(* 引理：|a_{n+1}/a_n| <= r 且 |a_N| = C => |a_n| <= C * r^{n-N}            *)
(* 由归纳：|a_{N+1}| = |a_{N+1}/a_N| * |a_N| <= r * C                      *)
(*         |a_{N+2}| = |a_{N+2}/a_{N+1}| * |a_{N+1}| <= r * C * r = C*r^2  *)
(******************************************************************************)

Lemma ratio_bound :
  forall (a : nat -> R) (r : R) (N : nat),
    0 <= r -> r < 1 ->
    (forall n, (N <= n)%nat -> a n <> 0) ->
    (forall n, (N <= n)%nat -> Rabs (a (S n) / a n) <= r) ->
    forall n, (N <= n)%nat ->
    Rabs (a n) <= Rabs (a N) * r ^ (n - N).
Proof.
  intros a r N Hr0 Hr1 Hnz Hratio n Hn.
  revert n Hn. induction n as [|n IH].
  - (* n = N *)
    intro Hn. simpl (n - N).
    assert (Hn_N : (N <= N)%nat) by lia.
    rewrite Rmult_1_r. apply Rle_refl.
  - (* n = S n' *)
    intro Hn.
    assert (Hn_N : (N <= n)%nat) by lia.
    assert (HIH : Rabs (a n) <= Rabs (a N) * r ^ (n - N)) by apply IH.
    (* |a_{S n}| = |a_{S n} / a_n| * |a_n| <= r * |a_n| <= r * C * r^{n-N} *)
    assert (Hratio_n : Rabs (a (S n) / a n) <= r) by apply Hratio.
    assert (Hnz_n : a n <> 0) by apply Hnz.
    assert (Habs_div : Rabs (a (S n) / a n) = Rabs (a (S n)) * / Rabs (a n)).
    { unfold Rdiv. rewrite Rabs_mult. rewrite Rabs_Rinv_depr. reflexivity. apply Hnz_n. }
    rewrite Habs_div in Hratio_n.
    assert (Habs_n_pos : 0 < Rabs (a n)).
    { apply Rabs_pos_lt. exact Hnz_n. }
    assert (Habs_SN : Rabs (a (S n)) <= Rabs (a n) * r).
    { apply Rmult_le_reg_l with (/ Rabs (a n)).
      - apply Rinv_0_lt_compat. exact Habs_n_pos.
      - rewrite Rmult_assoc. rewrite Rinv_r.
        + rewrite Rmult_1_l. exact Hratio_n.
        + apply Rgt_not_eq. exact Habs_n_pos. }
    assert (Hr_n_pos : 0 < r ^ (n - N)).
    { apply pow_lt. lra. }
    assert (Hr_pos : 0 < r) by lra.
    apply Rle_trans with (Rabs (a n) * r).
    - exact Habs_SN.
    - apply Rmult_le_compat_l.
      + apply Rabs_pos.
      + exact HIH.
Qed.

(******************************************************************************)
(* 引理：Rabs(a_N) * r^{n-N} = Rabs(a_N) * r^n / r^N                        *)
(******************************************************************************)

Lemma abs_N_r_shift :
  forall (a : nat -> R) (r : R) (N n : nat),
    0 < r -> (N <= n)%nat ->
    Rabs (a N) * r ^ (n - N) = Rabs (a N) * r ^ n * / r ^ N.
Proof.
  intros a r N n Hr Hn.
  assert (HrN_pos : 0 < r ^ N). { apply pow_lt. exact Hr. }
  assert (HrN_ne : r ^ N <> 0). { apply Rgt_not_eq. exact HrN_pos. }
  assert (Hrn_pos : 0 < r ^ n). { apply pow_lt. exact Hr. }
  assert (Hpow : r ^ (n - N) * r ^ N = r ^ n).
  { assert (H : n - N + N = n) by lia.
    rewrite H. rewrite pow_add. reflexivity. }
  unfold Rdiv. rewrite Rmult_assoc.
  rewrite <- (Rmult_comm (Rabs (a N))).
  rewrite Rmult_assoc.
  rewrite <- Rmult_assoc with (r ^ (n - N)) (r ^ N) (/ r ^ N).
  rewrite Rinv_r.
  - rewrite Rmult_1_r. rewrite Hpow. rewrite Rmult_comm. reflexivity.
  - exact HrN_ne.
Qed.

(******************************************************************************)
(* 比率收敛法 — 收敛部分                                                       *)
(* 若存在 0 <= r < 1 和 N 使得 n >= N 时 |a_{n+1}/a_n| <= r                 *)
(* 则 sum a_n 绝对收敛                                                        *)
(******************************************************************************)

Theorem ratio_test_convergent :
  forall (a : nat -> R) (r : R),
    0 <= r -> r < 1 ->
    (exists N : nat, forall n : nat, (N <= n)%nat ->
      a n <> 0 /\ Rabs (a (S n) / a n) <= r) ->
    series_cv a.
Proof.
  intros a r Hr0 Hr1 [N HN].
  assert (Hnz : forall n, (N <= n)%nat -> a n <> 0).
  { intros n Hn. destruct (HN n Hn) as [Hnz _]. exact Hnz. }
  assert (Hratio : forall n, (N <= n)%nat -> Rabs (a (S n) / a n) <= r).
  { intros n Hn. destruct (HN n Hn) as [_ Hratio]. exact Hratio. }
  assert (Hr_pos : 0 < r) by lra.
  assert (Hbound : forall n, (N <= n)%nat -> Rabs (a n) <= Rabs (a N) * r ^ (n - N)).
  { apply ratio_bound; [exact Hr0 | exact Hr1 | exact Hnz | exact Hratio]. }
  assert (Hr_abs : Rabs r < 1).
  { apply Rle_lt_trans with r; [apply Rabs_pos | exact Hr1]. }
  assert (Hgeo : series_cv (fun n => r ^ n)).
  { apply geometric_series_cv. exact Hr_abs. }
  assert (Habs_N_pos : 0 < Rabs (a N)).
  { apply Rabs_pos_lt. apply Hnz. lia. }
  assert (Habs_N_nonneg : 0 <= Rabs (a N)).
  { apply Rlt_le. exact Habs_N_pos. }
  assert (Hscal : series_cv (fun n => Rabs (a N) * r ^ n)).
  { apply series_scal_cv. exact Hgeo. }
  assert (Habs : forall n, Rabs (a n) <= (fun n => Rabs (a N) * r ^ n) n).
  { intro n. destruct (le_dec N n) as [Hle | Hgt].
    - assert (Hb : Rabs (a n) <= Rabs (a N) * r ^ (n - N)) by apply Hbound.
      rewrite abs_N_r_shift.
      + exact Hb.
      + exact Hr_pos.
      + exact Hle.
    - assert (Hr_n_pos : 0 <= r ^ n) by (apply pow_le; exact Hr0).
      apply Rle_trans with (Rabs (a N) * r ^ N).
      + apply Rabs_pos.
      + assert (Hr_N_pos : 0 <= r ^ N) by (apply pow_le; exact Hr0).
        assert (Hn_lt_N : (n < N)%nat) by lia.
        assert (Hr_n_le_N : r ^ n <= r ^ N).
        { revert n Hn_lt_N. induction n as [|n IH]; intros Hn.
          - lia.
          - destruct (Nat.eq_dec n (N - 1)) as [Heq | Hneq].
            * subst. assert (H : N = S (N - 1)) by lia. rewrite H. simpl.
              apply Rmult_le_compat_l; [exact Hr0 | apply Rle_refl].
            * assert (Hn_lt : (n < N - 1)%nat) by lia.
              assert (HIH : r ^ n <= r ^ (N - 1)) by apply IH.
              simpl. apply Rle_trans with (r * r ^ (N - 1)).
              -- apply Rmult_le_compat_l; [exact Hr0 | exact HIH].
              -- rewrite Rmult_comm. apply Rmult_le_compat_l; [exact Hr0 | apply Rle_refl]. }
        apply Rmult_le_compat_l; [exact Habs_N_nonneg | exact Hr_n_le_N]. }
  assert (Hcnneg : forall n, (fun n => Rabs (a N) * r ^ n) n >= 0).
  { intro n. unfold Rdiv. apply Rmult_le_compat_l.
    - apply Rabs_pos.
    - apply pow_le. exact Hr0. }
  apply comparison_test; [exact Habs | exact Hcnneg | exact Hscal].
Qed.

(******************************************************************************)
(* 比率收敛法 — 发散部分                                                       *)
(* 若存在 N 使得 n >= N 时 |a_{n+1}/a_n| >= 1                               *)
(* 则 |a_n| 递增且不趋于 0，sum a_n 发散                                      *)
(******************************************************************************)

Theorem ratio_test_divergent :
  forall (a : nat -> R),
    (exists N : nat, forall n : nat, (N <= n)%nat ->
      a n <> 0 /\ Rabs (a (S n) / a n) >= 1) ->
    ~ series_cv a.
Proof.
  intros a [N HN] Hcv.
  assert (Hnz : forall n, (N <= n)%nat -> a n <> 0).
  { intros n Hn. destruct (HN n Hn) as [Hnz _]. exact Hnz. }
  (* |a_n| 递增对 n >= N *)
  assert (Hgrowing : forall n, (N <= n)%nat -> Rabs (a n) <= Rabs (a (S n))).
  { intros n Hn.
    assert (Hratio : Rabs (a (S n) / a n) >= 1) by apply (HN n Hn).
    assert (Habs_n_pos : 0 < Rabs (a n)).
    { apply Rabs_pos_lt. apply Hnz. exact Hn. }
    assert (Habs_div : Rabs (a (S n) / a n) = Rabs (a (S n)) * / Rabs (a n)).
    { unfold Rdiv. rewrite Rabs_mult. rewrite Rabs_Rinv_depr. reflexivity. apply Hnz. exact Hn. }
    rewrite Habs_div in Hratio.
    apply Rmult_le_reg_l with (Rabs (a n)).
    - apply Rlt_le. exact Habs_n_pos.
    - rewrite Rmult_0_r. rewrite Rmult_comm. rewrite Rmult_assoc.
      rewrite Rinv_r.
      + rewrite Rmult_1_l. lra.
      + apply Rgt_not_eq. exact Habs_n_pos. }
  (* |a_n| >= |a_N| > 0 对 n >= N *)
  assert (Habs_ge : forall n, (N <= n)%nat -> Rabs (a n) >= Rabs (a N)).
  { intros n Hn. revert n Hn. induction n as [|n IH].
    - intro _. apply Rge_refl.
    - intro Hn.
      assert (Hn_N : (N <= n)%nat) by lia.
      assert (HIH : Rabs (a n) >= Rabs (a N)) by apply IH.
      assert (Hgrow : Rabs (a n) <= Rabs (a (S n))) by apply Hgrowing.
      lra. }
  assert (Habs_N_pos : 0 < Rabs (a N)).
  { apply Rabs_pos_lt. apply Hnz. lia. }
  (* a_n 不趋于 0 *)
  assert (Hnot_tendsto_0 : ~ Un_cv (fun n => a n) 0).
  { intro H0. unfold Un_cv, Rdist in H0.
    specialize (H0 (Rabs (a N)) Habs_N_pos) as [M HM].
    set (k := max N M).
    assert (Hk_N : (N <= k)%nat) by lia.
    assert (Hk_M : (k >= M)%nat) by lia.
    specialize (HM k Hk_M). unfold Rdist in HM.
    assert (Habs_k : Rabs (a k) >= Rabs (a N)) by apply Habs_ge.
    assert (Hd : Rdist (a k) 0 = Rabs (a k)).
    { unfold Rdist. rewrite Rminus_0_r. reflexivity. }
    rewrite Hd in HM. lra. }
  assert (Htendsto_0 : Un_cv (fun n => a n) 0).
  { apply series_cv_tendsto_0. exact Hcv. }
  apply Hnot_tendsto_0. exact Htendsto_0.
Qed.

(******************************************************************************)
(* 比率收敛法 — 极限版本                                                      *)
(* 若 lim |a_{n+1}/a_n| = L                                                  *)
(*   L < 1 => 收敛, L > 1 => 发散                                            *)
(******************************************************************************)

Axiom ratio_limit : (nat -> R) -> R.

Axiom ratio_limit_spec :
  forall (a : nat -> R) (L : R),
    ratio_limit a = L ->
    Un_cv (fun n => Rabs (a (S n) / a n)) L ->
    (L < 1 -> series_cv a) /\
    (L > 1 -> ~ series_cv a).

Theorem ratio_test_limit :
  forall (a : nat -> R) (L : R),
    (forall n, a n <> 0) ->
    Un_cv (fun n => Rabs (a (S n) / a n)) L ->
    (L < 1 -> series_cv a) /\
    (L > 1 -> ~ series_cv a).
Admitted.
