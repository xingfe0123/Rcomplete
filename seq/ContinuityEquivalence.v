From Stdlib Require Import Reals RIneq Ranalysis.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import Rfunctions.
From Stdlib Require Import Rseries.
From Stdlib Require Import SeqProp.
From Stdlib Require Import Compare_dec.
From Stdlib Require Import Rlimit.
From Stdlib Require Import Rderiv.

Open Scope R_scope.

(******************************************************************************)
(* 度量空间定义                                                                *)
(******************************************************************************)

Record MetricSpace : Type := BuildMetricSpace {
  Carrier : Type;
  dist : Carrier -> Carrier -> R;
  dist_pos : forall x y, 0 <= dist x y;
  dist_sym : forall x y, dist x y = dist y x;
  dist_tri : forall x y z, dist x z <= dist x y + dist y z;
  dist_refl : forall x y, dist x y = 0 <-> x = y
}.

(******************************************************************************)
(* 开球定义                                                                    *)
(******************************************************************************)

Definition open_ball (ms : MetricSpace) (x : @Carrier ms) (eps : R) : @Carrier ms -> Prop :=
  fun y => @dist ms x y < eps.

Definition closed_ball (ms : MetricSpace) (x : @Carrier ms) (eps : R) : @Carrier ms -> Prop :=
  fun y => @dist ms x y <= eps.

(******************************************************************************)
(* 邻域定义                                                                    *)
(******************************************************************************)

Definition neighbourhood (ms : MetricSpace) (x : @Carrier ms) (V : @Carrier ms -> Prop) : Prop :=
  exists eps : R, eps > 0 /\ forall y, @dist ms x y < eps -> V y.

(******************************************************************************)
(* 开集定义                                                                    *)
(******************************************************************************)

Definition open_set (ms : MetricSpace) (U : @Carrier ms -> Prop) : Prop :=
  forall x, U x -> neighbourhood ms x U.

(******************************************************************************)
(* ε-δ 连续性定义                                                              *)
(******************************************************************************)

Definition continuous_eps_delta (ms1 ms2 : MetricSpace) (f : @Carrier ms1 -> @Carrier ms2) : Prop :=
  forall (x : @Carrier ms1) (eps : R), eps > 0 ->
    exists delta : R, delta > 0 /\
      forall y, @dist ms1 x y < delta -> @dist ms2 (f x) (f y) < eps.

(******************************************************************************)
(* 原像连续性定义                                                              *)
(* f 连续 ⟺ 对 f(x) 的每个邻域 W，存在 x 的邻域 V 使得 f(V) ⊆ W            *)
(******************************************************************************)

Definition continuous_preimage (ms1 ms2 : MetricSpace) (f : @Carrier ms1 -> @Carrier ms2) : Prop :=
  forall (x : @Carrier ms1) (W : @Carrier ms2 -> Prop),
    neighbourhood ms2 (f x) W ->
    exists V : @Carrier ms1 -> Prop,
      neighbourhood ms1 x V /\ (forall y, V y -> W (f y)).

(******************************************************************************)
(* 开集原像连续性定义                                                          *)
(* f 连续 ⟺ 对每个开集 U，f⁻¹(U) 是开集                                     *)
(******************************************************************************)

Definition continuous_open_preimage (ms1 ms2 : MetricSpace) (f : @Carrier ms1 -> @Carrier ms2) : Prop :=
  forall (U : @Carrier ms2 -> Prop),
    open_set ms2 U -> open_set ms1 (fun x => U (f x)).

(******************************************************************************)
(* ============================================================================*)
(* 主定理 1：ε-δ 连续 ⟺ 原像邻域连续                                        *)
(* ============================================================================*)

Theorem continuous_eps_delta_iff_preimage :
  forall (ms1 ms2 : MetricSpace) (f : @Carrier ms1 -> @Carrier ms2),
    continuous_eps_delta ms1 ms2 f <-> continuous_preimage ms1 ms2 f.
Proof.
  intros ms1 ms2 f. split.
  - (* ε-δ ⟹ 原像 *)
    intros Hed x W [eps [Heps HW]].
    destruct (Hed x eps Heps) as [delta [Hdelta Hd]].
    exists (open_ball ms1 x delta).
    split.
    + exists delta. split. exact Hdelta. intros y Hy. exact Hy.
    + intros y Hy. apply HW. apply Hd. exact Hy.
  - (* 原像 ⟹ ε-δ *)
    intros Hpre x eps Heps.
    assert (HW : neighbourhood ms2 (f x) (open_ball ms2 (f x) eps)).
    { exists eps. split. exact Heps. intros y Hy. exact Hy. }
    destruct (Hpre x (open_ball ms2 (f x) eps) HW) as [V [HV HVf]].
    destruct HV as [delta [Hdelta HdV]].
    exists delta. split. exact Hdelta.
    intros y Hy.
    apply HVf. apply HdV. exact Hy.
Qed.

(******************************************************************************)
(* ============================================================================*)
(* 主定理 2：原像邻域连续 ⟺ 开集原像连续                                    *)
(* ============================================================================*)

Theorem continuous_preimage_iff_open_preimage :
  forall (ms1 ms2 : MetricSpace) (f : @Carrier ms1 -> @Carrier ms2),
    continuous_preimage ms1 ms2 f <-> continuous_open_preimage ms1 ms2 f.
Proof.
  intros ms1 ms2 f. split.
  - (* 原像 ⟹ 开集原像 *)
    intros Hpre U Hopen_U x Hfx_U.
    assert (HW : neighbourhood ms2 (f x) U).
    { apply Hopen_U. exact Hfx_U. }
    destruct (Hpre x U HW) as [V [HV HVf]].
    exists V. split.
    + exact HV.
    + intros y Hy. apply HVf. exact Hy.
  - (* 开集原像 ⟹ 原像 *)
    intros Hopen x W [eps [Heps HW]].
    assert (Hopen_ball : open_set ms2 (open_ball ms2 (f x) eps)).
    { intros z Hz.
      assert (Hz_in : open_ball ms2 (f x) eps z) by exact Hz.
      assert (Hfz : @dist ms2 (f x) z < eps) by exact Hz_in.
      assert (Hrem : eps - @dist ms2 (f x) z > 0) by lra.
      exists (eps - @dist ms2 (f x) z). split.
      + exact Hrem.
      + intros y Hy.
        apply Rlt_le_trans with (@dist ms2 (f x) z + @dist ms2 z y).
        * apply @dist_tri ms2.
        * lra. }
    assert (Hpre_open : open_set ms1 (fun x0 => open_ball ms2 (f x) eps (f x0))).
    { apply Hopen. exact Hopen_ball. }
    assert (Hfx_in_ball : open_ball ms2 (f x) eps (f x)).
    { assert (Hd0 : @dist ms2 (f x) (f x) = 0).
      { apply (@dist_refl ms2). reflexivity. }
      lra. }
    destruct (Hpre_open x Hfx_in_ball) as [delta [Hdelta HdV]].
    exists (open_ball ms1 x delta).
    split.
    + exists delta. split. exact Hdelta. intros y Hy. exact Hy.
    + intros y Hy.
      apply HW. apply HdV. exact Hy.
Qed.

(******************************************************************************)
(* ============================================================================*)
(* 主定理 3：ε-δ 连续 ⟺ 开集原像连续（综合）                                *)
(* ============================================================================*)

Theorem continuous_eps_delta_iff_open_preimage :
  forall (ms1 ms2 : MetricSpace) (f : @Carrier ms1 -> @Carrier ms2),
    continuous_eps_delta ms1 ms2 f <-> continuous_open_preimage ms1 ms2 f.
Proof.
  intros ms1 ms2 f. split.
  - intros Hed U Hopen x HUfx.
    assert (Hpre := continuous_eps_delta_iff_preimage ms1 ms2 f).
    destruct (Hpre 1) as Hpre.
    apply Hpre. exact Hed.
    apply Hopen. exact HUfx.
  - intros Hopen x eps Heps.
    assert (Hpre := continuous_preimage_iff_open_preimage ms1 ms2 f).
    destruct (Hpre 2) as Hpre.
    apply Hpre. exact Hopen.
    exists eps. split. exact Heps.
    intros y Hy. exact Hy.
Qed.

(******************************************************************************)
(* ============================================================================*)
(* R 上的具体版本                                                              *)
(* ============================================================================*)

Definition R_continuous_eps_delta (f : R -> R) : Prop :=
  forall (x : R) (eps : R), eps > 0 ->
    exists delta : R, delta > 0 /\
      forall y, Rabs (y - x) < delta -> Rabs (f y - f x) < eps.

Definition R_continuous_preimage (f : R -> R) : Prop :=
  forall (x : R) (W : R -> Prop),
    (exists eps : R, eps > 0 /\ forall y, Rabs (y - f x) < eps -> W y) ->
    exists V : R -> Prop,
      (exists delta : R, delta > 0 /\ forall y, Rabs (y - x) < delta -> V y) /\
      (forall y, V y -> W (f y)).

Definition R_open_set (U : R -> Prop) : Prop :=
  forall x, U x -> exists eps : R, eps > 0 /\ forall y, Rabs (y - x) < eps -> U y.

Definition R_continuous_open_preimage (f : R -> R) : Prop :=
  forall (U : R -> Prop), R_open_set U -> R_open_set (fun x => U (f x)).

(******************************************************************************)
(* R 上的度量空间实例                                                          *)
(******************************************************************************)

Lemma Rabs_eq_0_impl : forall r, Rabs r = 0 -> r = 0.
Proof.
  intros r H.
  destruct (Rle_dec 0 r) as [Hr | Hr].
  - rewrite (Rabs_right r (Rle_ge _ _ Hr)) in H. exact H.
  - assert (Hr_neg : r < 0) by lra.
    rewrite (Rabs_left r Hr_neg) in H.
    rewrite <- H. lra.
Qed.

Lemma Rdist_refl_iff : forall x y, Rdist x y = 0 <-> x = y.
Proof.
  intros x y. unfold Rdist. split.
  - intro H. apply Rminus_diag_uniq. apply Rabs_eq_0_impl. exact H.
  - intro H. rewrite H. rewrite Rminus_diag_right. rewrite Rabs_R0. reflexivity.
Qed.

Definition R_metric : MetricSpace :=
  BuildMetricSpace R Rdist
    (fun x y => Rabs_pos (y - x))
    Rdist_sym
    (fun x y z => Rabs_triang (y - x) (z - y))
    Rdist_refl_iff.

(******************************************************************************)
(* R 上 ε-δ ⟺ 原像邻域连续                                                  *)
(******************************************************************************)

Theorem R_continuous_eps_delta_iff_preimage :
  forall (f : R -> R),
    R_continuous_eps_delta f <-> R_continuous_preimage f.
Proof.
  intros f. split.
  - intros Hed x W [eps [Heps HW]].
    destruct (Hed x eps Heps) as [delta [Hdelta Hd]].
    exists (fun y => Rabs (y - x) < delta).
    split.
    + exists delta. split. exact Hdelta. intros y Hy. exact Hy.
    + intros y Hy. apply HW. apply Hd. exact Hy.
  - intros Hpre x eps Heps.
    assert (HW : (exists eps0 : R, eps0 > 0 /\ forall y, Rabs (y - f x) < eps0 -> Rabs (y - f x) < eps)).
    { exists eps. split. exact Heps. intros y Hy. exact Hy. }
    destruct (Hpre x (fun y => Rabs (y - f x) < eps) HW) as [V [[delta [Hdelta HdV]] HVf]].
    exists delta. split. exact Hdelta.
    intros y Hy. apply HVf. apply HdV. exact Hy.
Qed.

(******************************************************************************)
(* R 上原像邻域 ⟺ 开集原像连续                                              *)
(******************************************************************************)

Theorem R_continuous_preimage_iff_open_preimage :
  forall (f : R -> R),
    R_continuous_preimage f <-> R_continuous_open_preimage f.
Proof.
  intros f. split.
  - intros Hpre U Hopen_U x Hfx_U.
    assert (HW : exists eps : R, eps > 0 /\ forall y, Rabs (y - f x) < eps -> U y).
    { apply Hopen_U. exact Hfx_U. }
    destruct (Hpre x U HW) as [V [[delta [Hdelta HdV]] HVf]].
    exists delta. split. exact Hdelta.
    intros y Hy. apply HVf. apply HdV. exact Hy.
  - intros Hopen x W [eps [Heps HW]].
    assert (Hopen_ball : R_open_set (fun y => Rabs (y - f x) < eps)).
    { intros z Hz.
      assert (Hrem : eps - Rabs (z - f x) > 0) by lra.
      exists (eps - Rabs (z - f x)). split.
      + exact Hrem.
      + intros y Hy.
        apply Rlt_le_trans with (Rabs (z - f x) + Rabs (y - z)).
        * rewrite <- (Rabs_Ropp (z - f x)). rewrite Ropp_minus_distr.
          apply Rabs_triang.
        * lra. }
    assert (Hpre_open : R_open_set (fun x0 => Rabs (f x0 - f x) < eps)).
    { apply Hopen. exact Hopen_ball. }
    assert (Hfx_in : Rabs (f x - f x) < eps).
    { rewrite Rminus_diag_right. rewrite Rabs_R0. exact Heps. }
    destruct (Hpre_open x Hfx_in) as [delta [Hdelta HdV]].
    exists (fun y => Rabs (y - x) < delta).
    split.
    + exists delta. split. exact Hdelta. intros y Hy. exact Hy.
    + intros y Hy. apply HW. apply HdV. exact Hy.
Qed.

(******************************************************************************)
(* R 上 ε-δ ⟺ 开集原像连续（综合）                                          *)
(******************************************************************************)

Theorem R_continuous_eps_delta_iff_open_preimage :
  forall (f : R -> R),
    R_continuous_eps_delta f <-> R_continuous_open_preimage f.
Proof.
  intros f. split.
  - intros Hed U Hopen x HUfx.
    assert (Hpre := R_continuous_eps_delta_iff_preimage f).
    destruct (Hpre 1) as Hpre.
    apply Hpre. exact Hed. exact Hopen. exact HUfx.
  - intros Hopen x W HW.
    assert (Hpre := R_continuous_preimage_iff_open_preimage f).
    destruct (Hpre 2) as Hpre.
    apply Hpre. exact Hopen. exact HW.
Qed.

(******************************************************************************)
(* ============================================================================*)
(* 与标准库 continuity_pt 的等价性                                            *)
(* ============================================================================*)

Theorem R_continuous_eps_delta_iff_continuity_pt :
  forall (f : R -> R) (x : R),
    (forall eps, eps > 0 -> exists delta, delta > 0 /\
      forall y, Rabs (y - x) < delta -> Rabs (f y - f x) < eps) <->
    continuity_pt f x.
Proof.
  intros f x. split.
  - intros Hed.
    unfold continuity_pt, continue_in, limit1_in, limit_in. simpl.
    intros eps Heps.
    destruct (Hed eps Heps) as [delta [Hdelta Hd]].
    exists delta. split. exact Hdelta.
    intros y [Hy Dy].
    unfold Rdist in *.
    apply Hd. exact Hy.
  - intros Hcont eps Heps.
    unfold continuity_pt, continue_in, limit1_in, limit_in in Hcont. simpl in Hcont.
    destruct (Hcont eps Heps) as [delta [Hdelta Hd]].
    exists delta. split. exact Hdelta.
    intros y Hy.
    destruct (Req_dec y x) as [Heq | Hneq].
    + rewrite Heq. rewrite Rminus_diag_right. rewrite Rabs_R0. exact Heps.
    + apply Hd. split. exact Hy. exact Hneq.
Qed.
