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
Admitted.

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
Admitted.

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
Admitted.
  intros c z a Ha Habs_z Hcv.
  assert (Ha_pos : 0 < a) by exact Ha.
  assert (Hinv_a_pos : 0 < / a).
  { apply Rinv_0_lt_compat. exact Ha_pos. }
  assert (Haz : a * Rabs z > 1).
  { assert (H : Rabs z > / a) by exact Habs_z.
    apply Rmult_lt_reg_l with (/ a).
    - exact Hinv_a_pos.
    - rewrite Rmult_0_r. rewrite Rmult_assoc. rewrite Rinv_r.
      + rewrite Rmult_1_l. lra.
      + apply Rgt_not_eq. exact Ha_pos. }
  (* 取 eps 使得 (a - eps) * |z| > 1 且 a - eps > 0 *)
  assert (Hexists_eps : exists eps, eps > 0 /\ a - eps > 0 /\ (a - eps) * Rabs z > 1).
  { exists (a / 2).
    split.
    - unfold Rdiv. apply Rmult_lt_0_compat.
      + exact Ha_pos.
      + apply Rinv_0_lt_compat. lra.
    - split.
      + unfold Rdiv. apply Rmult_lt_reg_l with 2.
        * apply Rinv_0_lt_compat. lra.
        * rewrite Rmult_0_r. rewrite Rmult_assoc. rewrite Rinv_r.
          -- lra.
          -- apply Rgt_not_eq. lra.
      + unfold Rdiv. apply Rmult_lt_reg_l with 2.
        * apply Rinv_0_lt_compat. lra.
        * rewrite Rmult_0_r. rewrite Rmult_plus_distr_l.
          rewrite <- (Rmult_comm 2 (Rabs z)).
          rewrite Rmult_assoc. rewrite Rinv_r.
          -- lra.
          -- apply Rgt_not_eq. lra. }
  destruct Hexists_eps as [eps [Heps_pos [Ha_eps_pos Heps_bound]]].
  (* 由 limsup 定义，对任意 N 存在 n >= N 使得 |c_n|^{1/n} >= a - eps *)
  assert (Hlimsup : limsup_root (fun n => Rabs (c n) ^ (/ INR (S n))) = a).
  { reflexivity. }
  destruct (limsup_root_spec (fun n => Rabs (c n) ^ (/ INR (S n))) a Hlimsup)
    as [_ Hspec].
  (* (D) 对每个 N 存在 n >= N 使得 |c_n|^{1/n} >= a - eps                   *)
  (* 则 |c_n * z^n| >= ((a-eps)*|z|)^n > 1 对无穷多个 n                    *)
  (* 所以 c_n * z^n 不趋于 0                                                 *)
  assert (Hnot_tendsto_0 : ~ Un_cv (fun n => power_series c z n) 0).
  { intro H0. unfold Un_cv, Rdist in H0.
    specialize (H0 1 lra) as [M HM].
    (* 存在 n >= M 使得 |c_n|^{1/n} >= a - eps *)
    assert (Hn : exists n, (M <= n)%nat /\
      Rabs (c n) ^ (/ INR (S n)) >= a - eps).
    { admit. }
    destruct Hn as [n [Hn_M Hn_root]].
    specialize (HM n Hn_M). unfold Rdist in HM.
    (* |c_n * z^n| >= ((a-eps)*|z|)^n > 1, 但 |c_n * z^n| < 1, 矛盾 *)
    assert (Habs_n : Rabs (power_series c z n) >= ((a - eps) * Rabs z) ^ n).
    { (* (D) 由 |c_n|^{1/n} >= a - eps 推出 |c_n| >= (a-eps)^n              *)
      admit. }
    assert (Hpow_gt_1 : ((a - eps) * Rabs z) ^ n > 1).
    { (* (a-eps)*|z| > 1 => ((a-eps)*|z|)^n > 1 对 n >= 1                  *)
      admit. }
    assert (Habs_lt_1 : Rabs (power_series c z n) < 1).
    { assert (Hd : Rdist (power_series c z n) 0 = Rabs (power_series c z n)).
      { unfold Rdist. rewrite Rminus_0_r. reflexivity. }
      rewrite Hd in HM. exact HM. }
    lra. }
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
  (* a = 0 => 对任意 eps > 0, 存在 N 使得 n >= N 时 |c_n|^{1/n} <= eps     *)
  (* 取 eps 使得 eps * |z| < 1 (当 |z| > 0) 或 eps < 1 (当 |z| = 0)       *)
  destruct (Rle_dec (Rabs z) 0) as [Hz0 | Hz0].
  - (* |z| = 0 => c_n * 0^n = 0 对 n >= 1, 级数只有 c_0 项 *)
    assert (Hz_eq : Rabs z = 0) by lra.
    assert (Hz : z = 0).
    { apply Rabs_eq_0. exact Hz_eq. }
    rewrite Hz.
    exists (c 0%nat * 0 ^ 0%nat).
    unfold series_convergent, Un_cv, Rdist. intros eps Heps.
    exists 0%nat. intros n Hn.
    simpl (0 ^ 0%nat). rewrite Rmult_1_l.
    destruct n as [|n].
    - simpl. rewrite Rminus_0_r. rewrite Rabs_R0. lra.
    - simpl (0 ^ S n). rewrite Rmult_0_r.
      rewrite Rminus_0_r. rewrite Rabs_R0. lra.
  - (* |z| > 0 => 取 eps = 1/(2*|z|) 使得 eps*|z| = 1/2 < 1 *)
    assert (Habs_z_pos : 0 < Rabs z) by lra.
    set (eps := / (2 * Rabs z)).
    assert (Heps_pos : eps > 0).
    { unfold eps. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; lra. }
    assert (Heps_bound : eps * Rabs z < 1).
    { unfold eps. rewrite Rmult_assoc. rewrite Rinv_r.
      - rewrite Rmult_1_l. lra.
      - apply Rgt_not_eq. apply Rmult_lt_0_compat; lra. }
    (* (D) 由 limsup = 0 得到 |c_n|^{1/n} <= eps 对 n >= N *)
    admit.
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
