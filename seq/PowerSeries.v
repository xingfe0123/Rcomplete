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

(******************************************************************************)
(* 主定理 3：a = 0 时 R = +infty，对所有 z 收敛                              *)
(******************************************************************************)

Theorem power_series_convergent_infty :
  forall (c : nat -> R) (z : R),
    limsup_root (fun n => Rabs (c n) ^ (/ INR (S n))) = 0 ->
    series_cv (power_series c z).
Admitted.

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
