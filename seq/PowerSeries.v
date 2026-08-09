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
(* 幂级数定义                                                                  *)
(* power_series c z n = c_n * z^n                                             *)
(******************************************************************************)

Definition power_series (c : nat -> R) (z : R) (n : nat) : R :=
  c n * z ^ n.

(******************************************************************************)
(* 收敛半径定义                                                                *)
(* a = limsup_{n->infty} |c_n|^{1/n}                                         *)
(* R = 1/a  (a = 0 时 R = +infty, a = +infty 时 R = 0)                      *)
(******************************************************************************)

(* (D) limsup 定义 *)
Axiom limsup_root : (nat -> R) -> R.

Axiom limsup_root_spec :
  forall (f : nat -> R) (a : R),
    limsup_root f = a ->
    a >= 0 /\
    (forall eps, eps > 0 ->
      (exists N, forall n, (N <= n)%nat -> f n <= a + eps) /\
      (forall eps, eps > 0 ->
        forall N, exists n, (N <= n)%nat /\ f n >= a - eps)).

Definition convergence_radius (c : nat -> R) : R :=
  let a := limsup_root (fun n => Rabs (c n) ^ (/ INR (S n))) in
  match Rle_dec a 0 with
  | left _ => 0  (* a = 0 => R = +infty, 用 0 表示 *)
  | right _ => / a
  end.

(******************************************************************************)
(* 引理：|c_n * z^n| = |c_n| * |z|^n                                         *)
(******************************************************************************)

Lemma power_series_abs :
  forall (c : nat -> R) (z : R) (n : nat),
  Rabs (power_series c z n) = Rabs (c n) * Rabs z ^ n.
Proof.
  intros c z n. unfold power_series.
  rewrite Rabs_mult.
  rewrite <- Rabs_pow.
  reflexivity.
Qed.

(******************************************************************************)
(* 引理：|c_n|^{1/n} * |z| < 1 => |c_n| * |z|^n < 1                         *)
(* 即 |c_n| < 1/|z|^n = (1/|z|)^n                                           *)
(* 更精确：|c_n|^{1/n} <= a + eps, |z| < 1/(a+eps)                          *)
(* => |c_n| <= (a+eps)^n, |c_n|*|z|^n <= (a+eps)^n * |z|^n = ((a+eps)*|z|)^n *)
(* => (a+eps)*|z| < 1 => 几何级数收敛                                        *)
(******************************************************************************)

(******************************************************************************)
(* 引理：若 |c_n|^{1/n} <= r 且 r * |z| < 1                                  *)
(* 则 |c_n * z^n| <= (r * |z|)^n                                             *)
(******************************************************************************)

Lemma root_bound_power :
  forall (c : nat -> R) (r z : R) (N n : nat),
    0 <= r -> (N <= n)%nat ->
    Rabs (c n) ^ (/ INR (S n)) <= r ->
    Rabs (power_series c z n) <= (r * Rabs z) ^ n.
Proof.
  intros c r z N n Hr0 Hn Hroot.
  unfold power_series. rewrite Rabs_mult. rewrite <- Rabs_pow.
  assert (Hr_pos : 0 < r) by lra.
  assert (Hn_pos : 0 < INR (S n)).
  { apply lt_0_INR. lia. }
  assert (Hcn_abs_pos : 0 <= Rabs (c n)).
  { apply Rabs_pos. }
  assert (Hcn_abs_nonneg : 0 < Rabs (c n) \/ Rabs (c n) = 0).
  { destruct (Rabs (c n)) as [|x] eqn:Heq.
    - right. reflexivity.
    - left. apply Rlt_0_plus. }
  destruct Hcn_abs_nonneg as [Hcn_pos | Hcn_zero].
  - (* Rabs(c_n) > 0 *)
    assert (Hroot_pow : Rabs (c n) <= r ^ (S n)).
    { assert (H1 : Rabs (c n) = (Rabs (c n) ^ (/ INR (S n))) ^ (INR (S n))).
      { rewrite <- Rpow_Rpow.
        - reflexivity.
        - exact Hcn_pos. }
      rewrite H1.
      assert (H2 : r ^ (INR (S n)) = r ^ (S n)).
      { rewrite <- Rpow_nat_Rpow.
        - reflexivity.
        - exact Hr_pos. }
      rewrite H2.
      apply Rpow_le2; [exact Hroot | exact Hr0]. }
    assert (Hz_abs_nonneg : 0 <= Rabs z) by apply Rabs_pos.
    apply Rle_trans with (r ^ (S n) * Rabs z ^ n).
    - apply Rmult_le_compat_r; [exact Hz_abs_nonneg | exact Hroot_pow].
    - assert (H3 : r ^ (S n) * Rabs z ^ n = r * (r ^ n * Rabs z ^ n)).
      { simpl. rewrite Rmult_assoc. reflexivity. }
      rewrite H3. rewrite <- Rpow_pow_Rpow.
      + rewrite Rmult_assoc. rewrite <- Rpow_add.
        * f_equal. lia.
        * exact Hr_pos.
        * apply Rabs_pos.
      + exact Hr_pos.
      + apply Rabs_pos.
  - (* Rabs(c_n) = 0 *)
    rewrite Hcn_zero. rewrite Rmult_0_l.
    assert (Hz_abs_nonneg : 0 <= Rabs z) by apply Rabs_pos.
    assert (Hr_z_nonneg : 0 <= r * Rabs z).
    { apply Rmult_le_compat; [exact Hr0 | exact Hz_abs_nonneg]. }
    apply Rle_trans with (0 * (r * Rabs z) ^ n).
    - lra.
    - rewrite Rmult_0_l. apply Rle_refl.
Qed.

(******************************************************************************)
(* 主定理 1：|z| < R 时幂级数绝对收敛                                         *)
(*                                                                            *)
(* 证明：设 a = limsup |c_n|^{1/n}, R = 1/a                                 *)
(* |z| < R = 1/a => a * |z| < 1                                             *)
(* 取 eps 使得 a + eps < 1/|z|, 即 (a+eps)*|z| < 1                          *)
(* 由 limsup 定义，存在 N 使得 n >= N 时 |c_n|^{1/n} <= a + eps             *)
(* 所以 |c_n * z^n| <= ((a+eps)*|z|)^n, 几何级数收敛                        *)
(******************************************************************************)

Theorem power_series_convergent :
  forall (c : nat -> R) (z : R),
    let a := limsup_root (fun n => Rabs (c n) ^ (/ INR (S n))) in
    a > 0 ->
    Rabs z < / a ->
    series_cv (power_series c z).
Proof.
  intros c z a Ha Habs.
  assert (Ha_pos : 0 < a) by exact Ha.
  assert (Hz_abs_nonneg : 0 <= Rabs z) by apply Rabs_pos.
  assert (Haz : a * Rabs z < 1).
  { assert (H1 : a * Rabs z < a * / a).
    { apply Rmult_lt_compat_l; [exact Ha_pos | exact Habs]. }
    rewrite Rmult_comm. rewrite Rinv_r in H1.
    - lra.
    - apply Rgt_not_eq. exact Ha_pos. }
  (* 取 eps 使得 (a + eps) * |z| < 1 *)
  assert (Heps_exists : exists eps, eps > 0 /\ (a + eps) * Rabs z < 1).
  { assert (Hdiff : 1 - a * Rabs z > 0) by lra.
    destruct (Rabs z) as [|xz] eqn:Heq_z.
    + rewrite Rabs_R0 in *. exists 1. split; lra.
    + assert (Hz_pos : 0 < Rabs z) by (apply Rabs_pos_lt; apply Rlt_0_plus).
      exists ((1 - a * Rabs z) / (2 * Rabs z)).
      * unfold Rdiv. apply Rmult_lt_0_compat; [lra |].
        apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; lra.
      * rewrite Rmult_plus_distr_l.
        rewrite Rmult_assoc. rewrite Rinv_r.
        -- rewrite Rmult_1_r. lra.
        -- apply Rgt_not_eq. exact Hz_pos. }
  destruct Heps_exists as [eps [Heps_pos Heps_bound]].
  assert (Ha_eps_pos : 0 < a + eps) by lra.
  assert (Ha_eps_nonneg : 0 <= a + eps) by lra.
  assert (Heq : limsup_root (fun n => Rabs (c n) ^ (/ INR (S n))) = a) by reflexivity.
  destruct (limsup_root_spec (fun n => Rabs (c n) ^ (/ INR (S n))) a Heq) as [Hnneg [Hupper _]].
  destruct (Hupper eps Heps_pos) as [N HN].
  assert (Hr_z_lt_1 : Rabs ((a + eps) * Rabs z) < 1).
  { rewrite Rabs_mult.
    assert (H1 : Rabs (a + eps) = a + eps) by (apply Rabs_right; left; exact Ha_eps_pos).
    rewrite H1. exact Heps_bound. }
  assert (Hgeo : series_cv (fun n => ((a + eps) * Rabs z) ^ n)).
  { apply geometric_series_cv. exact Hr_z_lt_1. }
  (* 用 root_test_convergent：对 n >= N, |c_n * z^n| <= ((a+eps)*|z|)^n *)
  assert (Hr_z_nonneg : 0 <= (a + eps) * Rabs z).
  { apply Rmult_le_compat; [exact Ha_eps_nonneg | exact Hz_abs_nonneg]. }
  assert (Habs_tail : forall n, (N <= n)%nat ->
    Rabs (power_series c z n) <= ((a + eps) * Rabs z) ^ n).
  { intros n Hn. apply root_bound_power; [exact Ha_eps_nonneg | exact Hn | apply HN; exact Hn]. }
  apply root_test_convergent with (r := (a + eps) * Rabs z).
  - exact Hr_z_nonneg.
  - exact Heps_bound.
  - exists N. exact Habs_tail.
Qed.

(******************************************************************************)
(* 主定理 2：|z| > R 时幂级数发散                                             *)
(*                                                                            *)
(* 证明：a * |z| > 1                                                         *)
(* 由 limsup 定义，对任意 N 存在 n >= N 使得 |c_n|^{1/n} >= a - eps         *)
(* 取 eps 使得 (a - eps) * |z| > 1                                          *)
(* 则 |c_n * z^n| >= ((a-eps)*|z|)^n > 1 对无穷多个 n                      *)
(* 所以 c_n * z^n 不趋于 0，级数发散                                        *)
(******************************************************************************)

Theorem power_series_divergent :
  forall (c : nat -> R) (z : R),
    let a := limsup_root (fun n => Rabs (c n) ^ (/ INR (S n))) in
    a > 0 ->
    Rabs z > / a ->
    ~ series_cv (power_series c z).
Proof.
  intros c z a Ha Habs Hcv.
  assert (Ha_pos : 0 < a) by exact Ha.
  assert (Hz_abs_pos : 0 < Rabs z) by lra.
  assert (Haz : a * Rabs z > 1).
  { assert (H1 : a * Rabs z > a * / a).
    { apply Rmult_gt_compat_l; [exact Ha_pos | exact Habs]. }
    rewrite Rmult_comm. rewrite Rinv_r in H1.
    - lra.
    - apply Rgt_not_eq. exact Ha_pos. }
  assert (Heps_exists : exists eps, eps > 0 /\ (a - eps) * Rabs z > 1).
  { exists ((a * Rabs z - 1) / (2 * Rabs z)).
    - unfold Rdiv. apply Rmult_lt_0_compat; [lra |].
      apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; [exact Hz_abs_pos | lra].
    - rewrite Rmult_minus_distr_l.
      rewrite Rmult_assoc. rewrite Rinv_r.
      + rewrite Rmult_1_r. lra.
      + apply Rgt_not_eq. exact Hz_abs_pos. }
  destruct Heps_exists as [eps [Heps_pos Heps_bound]].
  assert (Ha_eps_pos : 0 < a - eps) by lra.
  assert (Ha_eps_nonneg : 0 <= a - eps) by lra.
  assert (Heq : limsup_root (fun n => Rabs (c n) ^ (/ INR (S n))) = a) by reflexivity.
  destruct (limsup_root_spec (fun n => Rabs (c n) ^ (/ INR (S n))) a Heq) as [Hnneg [_ Hlower]].
  (* 通项不趋于 0 *)
  assert (Hnot_tendsto_0 : ~ Un_cv (fun n => power_series c z n) 0).
  { intro H0. unfold Un_cv, Rdist in H0.
    assert (Hr_z_pos : 0 < (a - eps) * Rabs z) by lra.
    specialize (H0 (1 - 1)) as [M HM].
    - lra.
    - (* 对任意 M, 存在 n >= M 使得 |c_n|^{1/n} >= a - eps *)
      specialize (Hlower M) as [n [Hn Hroot_lower]].
      assert (Hn_M : (n >= M)%nat) by exact Hn.
      specialize (HM n Hn_M). unfold Rdist in HM.
      (* |c_n * z^n| >= ((a-eps)*|z|)^n > 1 *)
      assert (Habs_cn : Rabs (c n) >= (a - eps) ^ (S n)).
      { assert (H1 : Rabs (c n) = (Rabs (c n) ^ (/ INR (S n))) ^ (INR (S n))).
        { destruct (Rabs (c n)) as [|cn] eqn:Heq_cn.
          - rewrite Rabs_R0 in Heq_cn. rewrite Heq_cn. rewrite Rpow_R0.
            + reflexivity.
            + apply lt_0_INR. lia.
          - rewrite <- Rpow_Rpow; [reflexivity | apply Rlt_0_plus]. }
        rewrite H1.
        assert (H2 : (a - eps) ^ (INR (S n)) = (a - eps) ^ (S n)).
        { rewrite <- Rpow_nat_Rpow; [reflexivity | exact Ha_eps_pos]. }
        rewrite H2.
        apply Rpow_le2; [exact Hroot_lower | exact Ha_eps_nonneg]. }
      assert (Hps_abs : Rabs (power_series c z n) >= ((a - eps) * Rabs z) ^ n).
      { rewrite power_series_abs.
        assert (Hz_pow_pos : 0 <= Rabs z ^ n) by (apply pow_le; apply Rabs_pos).
        assert (Hcn_nonneg : 0 <= Rabs (c n)) by apply Rabs_pos.
        assert (Hcn_ge : Rabs (c n) >= (a - eps) ^ (S n)) by exact Habs_cn.
        assert (Hr_eps_n : (a - eps) ^ (S n) = (a - eps) * (a - eps) ^ n).
        { simpl. rewrite Rmult_assoc. reflexivity. }
        rewrite Hr_eps_n in Hcn_ge.
        apply Rle_trans with ((a - eps) * (a - eps) ^ n * Rabs z ^ n).
        - apply Rmult_le_compat; [exact Hcn_nonneg | exact Hz_pow_pos].
          exact Hcn_ge.
        - rewrite Rmult_assoc. rewrite <- Rmult_assoc with ((a - eps) ^ n) (Rabs z ^ n).
          f_equal. rewrite <- Rpow_pow_Rpow.
          + rewrite <- Rpow_add.
            * f_equal. lia.
            * exact Ha_eps_pos.
            * apply Rabs_pos.
          + exact Ha_eps_pos.
          + apply Rabs_pos. }
      assert (Hr_z_n_gt_1 : ((a - eps) * Rabs z) ^ n > 1).
      { assert (Hr_z_gt_1 : (a - eps) * Rabs z > 1) by exact Heps_bound.
        revert n Hn. induction n as [|n IH]; intros Hn.
        - lia.
        - assert (Hn_gt_0 : (n > 0)%nat) by lia.
          assert (HIH : ((a - eps) * Rabs z) ^ n > 1) by apply IH.
          simpl. apply Rmult_gt_compat_l; [lra | exact HIH]. }
      assert (Hps_gt_1 : Rabs (power_series c z n) > 1) by lra.
      assert (Hd : Rdist (power_series c z n) 0 = Rabs (power_series c z n)).
      { unfold Rdist. rewrite Rminus_0_r. reflexivity. }
      rewrite Hd in HM. lra. }
  assert (Htendsto_0 : Un_cv (fun n => power_series c z n) 0).
  { apply series_cv_tendsto_0. exact Hcv. }
  apply Hnot_tendsto_0. exact Htendsto_0.
Qed.

(******************************************************************************)
(* 主定理 3：a = 0 时 R = +infty，对所有 z 收敛                              *)
(******************************************************************************)

Theorem power_series_convergent_infty :
  forall (c : nat -> R) (z : R),
    limsup_root (fun n => Rabs (c n) ^ (/ INR (S n))) = 0 ->
    series_cv (power_series c z).
Proof.
  intros c z Ha.
  assert (Hz_abs_nonneg : 0 <= Rabs z) by apply Rabs_pos.
  destruct (Rabs z) as [|xz] eqn:Heq_z.
  - (* z = 0 *)
    rewrite Rabs_R0 in Heq_z.
    assert (Hps_0 : forall n, power_series c z n = c n * 0 ^ n).
    { intro n. unfold power_series. rewrite Heq_z. reflexivity. }
    assert (Hps_0_n : forall n, (0 < n)%nat -> power_series c z n = 0).
    { intros n Hn. rewrite Hps_0. simpl. lra. }
    assert (Hps_0_0 : power_series c z 0 = c 0).
    { rewrite Hps_0. simpl. lra. }
    exists (c 0). unfold series_convergent, Un_cv, Rdist. intros eps Heps.
    exists 1%nat. intro n. assert (Hn : (n >= 1)%nat) by lia.
    destruct n as [|n].
    - lia.
    - rewrite partial_sum_S. rewrite Hps_0_n; lia. rewrite Hps_0_0. lra.
  - (* z <> 0 *)
    assert (Hz_abs_pos : 0 < Rabs z) by (apply Rabs_pos_lt; apply Rlt_0_plus).
    (* a = 0, 对任意 r > 0, 存在 N 使得 n >= N 时 |c_n|^{1/n} <= r *)
    (* 取 r 使得 r * |z| < 1, 即 r < 1/|z| *)
    assert (Hinv_z_pos : 0 < / Rabs z).
    { apply Rinv_0_lt_compat. exact Hz_abs_pos. }
    assert (Hr_exists : exists r, 0 < r /\ r * Rabs z < 1).
    { exists (/ (2 * Rabs z)).
      - unfold Rdiv. apply Rmult_lt_0_compat; [lra |].
        apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; [exact Hz_abs_pos | lra].
      - rewrite Rmult_assoc. rewrite Rinv_r.
        + rewrite Rmult_1_r. lra.
        + apply Rgt_not_eq. apply Rmult_lt_0_compat; [exact Hz_abs_pos | lra]. }
    destruct Hr_exists as [r [Hr_pos Hr_bound]].
    assert (Hr_nonneg : 0 <= r) by lra.
    assert (Heq : limsup_root (fun n => Rabs (c n) ^ (/ INR (S n))) = 0) by exact Ha.
    destruct (limsup_root_spec (fun n => Rabs (c n) ^ (/ INR (S n))) 0 Heq) as [Hnneg [Hupper _]].
    destruct (Hupper r Hr_pos) as [N HN].
    assert (Habs_tail : forall n, (N <= n)%nat ->
      Rabs (power_series c z n) <= (r * Rabs z) ^ n).
    { intros n Hn. apply root_bound_power; [exact Hr_nonneg | exact Hn | apply HN; exact Hn]. }
    apply root_test_convergent with (r := r * Rabs z).
    - apply Rmult_le_compat; [exact Hr_nonneg | exact Hz_abs_nonneg].
    - exact Hr_bound.
    - exists N. exact Habs_tail.
Qed.

(******************************************************************************)
(* 综合定理：Cauchy-Hadamard                                                  *)
(******************************************************************************)

Theorem cauchy_hadamard :
  forall (c : nat -> R) (z : R),
    let a := limsup_root (fun n => Rabs (c n) ^ (/ INR (S n))) in
    (a = 0 -> series_cv (power_series c z)) /\
    (a > 0 -> Rabs z < / a -> series_cv (power_series c z)) /\
    (a > 0 -> Rabs z > / a -> ~ series_cv (power_series c z)).
Proof.
  intros c z a.
  split; [|split].
  - intro Ha. apply power_series_convergent_infty. exact Ha.
  - intros Ha Habs. apply power_series_convergent; [exact Ha | exact Habs].
  - intros Ha Habs. apply power_series_divergent; [exact Ha | exact Habs].
Qed.
