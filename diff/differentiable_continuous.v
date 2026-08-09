From Stdlib Require Import Reals Lra Ranalysis1.

Open Scope R_scope.

(* 区间 [a,b] *)
Definition in_interval (a b x : R) : Prop := a <= x <= b.

(* 连续性：ε-δ 定义 *)
Definition continuous_at (f : R -> R) (p : R) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, Rabs (x - p) < delta -> Rabs (f x - f p) < eps.

(* 可微性：存在导数 l 使得导数极限存在 *)
Definition differentiable_at (f : R -> R) (p : R) : Prop :=
  exists l, derivable_pt_lim f p l.

(* 定理：可微 => 连续 *)
Theorem differentiable_continuous : forall (f : R -> R) (a b x : R),
  in_interval a b x ->
  differentiable_at f x ->
  continuous_at f x.
Proof.
  intros f a b x _ Hdiff.
  unfold continuous_at.
  intros eps Heps.
  assert (Htmp_diff := Hdiff).
  destruct Htmp_diff as [l Hl].

  (* 第一步：用 eps=1 取 delta1，使 |(f(x+h)-f(x))/h - l| < 1 *)
  assert (Htmp := Hl 1 (Rlt_0_1)).
  destruct Htmp as [delta1 Htmp2].
  destruct Htmp2 as [Hdelta1_pos H1].

  (* 第二步：取 delta = min(delta1, eps/(|l|+1)) *)
  exists (Rmin delta1 (eps / (Rabs l + 1))).
  split.
  { apply Rmin_pos.
    - exact Hdelta1_pos.
    - apply Rlt_div_l.
      + apply Rlt_le_trans with 1; [apply Rlt_0_1 | apply Rle_refl].
      + lra. }

  intros x' Hx'.
  destruct (Req_dec x' x) as [Heq|Hneq].
  - (* 情形 1：x' = x，则 |f(x')-f(x)| = 0 < eps *)
    rewrite Heq.
    replace (f x - f x) with 0 by lra.
    rewrite Rabs_R0. exact Heps.

  - (* 情形 2：x' ≠ x *)
    set (h := x' - x).
    assert (Hh: h <> 0) by (unfold h; lra).
    assert (Hplus: x + h = x') by (unfold h; lra).

    (* 由可微性：|(f(x+h)-f(x))/h - l| < 1 *)
    assert (Hf1: Rabs ((f (x + h) - f x) / h - l) < 1).
    { apply (H1 h Hh).
      apply (Rmin_l _ _) in Hx'. exact Hx'. }

    (* 计算 |f(x')-f(x)| = |h * ((f(x+h)-f x)/h)| *)
    rewrite Hplus.
    replace (f (x + h) - f x) with (h * ((f (x + h) - f x) / h)) by (field; lra).

    (* |h * A| = |h| * |A| *)
    rewrite Rabs_mult.

    (* 证明 |h| * |(f(x+h)-f x)/h| < eps *)
    (* 先用 |(f(x+h)-f x)/h| <= |l| + 1 *)
    assert (Hbound: Rabs ((f (x + h) - f x) / h) <= Rabs l + 1).
    { unfold Rle. right.
      replace ((f (x + h) - f x) / h) with (((f (x + h) - f x) / h - l) + l) by lra.
      rewrite Rabs_triang.
      apply Rplus_lt_compat_l.
      exact Hf1. }

    (* |h| * |(f(x+h)-f x)/h| <= |h| * (|l|+1) < eps *)
    apply (Rle_lt_trans _ (Rabs h * (Rabs l + 1)) eps).
    + apply Rmult_le_compat_l.
      * exact Hbound.
      * apply Rabs_pos.
    + (* 证明 |h| * (|l|+1) < eps *)
      unfold h.
      apply (Rmin_r _ _) in Hx'.
      assert (Hlt: Rabs (x' - x) * (Rabs l + 1) < eps / (Rabs l + 1) * (Rabs l + 1)).
      { apply Rmult_lt_compat_r.
        - apply Rlt_le_trans with 1; [apply Rlt_0_1 | apply Rle_refl].
          exact Hx'. }
      assert (Hrw: eps / (Rabs l + 1) * (Rabs l + 1) = eps).
      { field. apply Rlt_le_trans with 1; [apply Rlt_0_1 | apply Rle_refl]. }
      rewrite Hrw in Hlt.
      exact Hlt.
Qed.

(* 推论：区间上可微 => 区间上每点连续 *)
Theorem differentiable_continuous_on_interval : forall (f : R -> R) (a b : R),
  (forall x, in_interval a b x -> differentiable_at f x) ->
  forall x, in_interval a b x -> continuous_at f x.
Proof.
  intros f a b Hdiff x' Hx'.
  apply (differentiable_continuous f a b x' Hx' (Hdiff x' Hx')).
Admitted.
