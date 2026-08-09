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
  destruct Hdiff as [l Hl].

  (* 第一步：用 eps=1 取 delta1 *)
  destruct (Hl 1 (Rlt_0_1)) as [delta1 H1].
  destruct delta1 as [delta1 Hdelta1_pos]. simpl in H1.

  (* 第二步：取 delta = min(delta1, eps/(|l|+1)) *)
  exists (Rmin delta1 (eps / (Rabs l + 1))).
  split.
  { apply Rmin_pos.
    - exact Hdelta1_pos.
    - assert (H: 0 <= Rabs l) by apply Rabs_pos.
      assert (H': Rabs l + 1 > 0) by lra.
      replace (eps / (Rabs l + 1)) with (eps * /(Rabs l + 1)).
      + apply Rmult_lt_0_compat; [exact Heps | apply Rinv_pos; exact H'].
      + unfold Rdiv; reflexivity. }

  intros x' Hx'.
  destruct (Req_dec x' x) as [Heq|Hneq].
  - (* 情形 1：x' = x *)
    rewrite Heq.
    replace (f x - f x) with 0 by lra.
    rewrite Rabs_R0. exact Heps.

  - (* 情形 2：x' ≠ x *)
    assert (Hh: x' - x <> 0) by lra.
    assert (Hx1: Rabs (x' - x) < delta1).
    { eapply Rlt_le_trans; [exact Hx' | apply Rmin_l]. }
    assert (Hx2: Rabs (x' - x) < eps / (Rabs l + 1)).
    { eapply Rlt_le_trans; [exact Hx' | apply Rmin_r]. }

    (* 由可微性：|(f(x')-f(x))/(x'-x) - l| < 1 *)
    assert (Hf1: Rabs ((f x' - f x) / (x' - x) - l) < 1).
    { replace (Rabs ((f x' - f x) / (x' - x) - l) < 1) with
        (Rabs ((f (x + (x' - x)) - f x) / (x' - x) - l) < 1).
      - apply (H1 (x' - x) Hh Hx1).
      - repeat f_equal; lra. }

    (* 证明 |(f(x')-f x)/(x'-x)| <= |l| + 1 *)
    assert (Hbound: Rabs ((f x' - f x) / (x' - x)) <= Rabs l + 1).
    { unfold Rle. left.
      apply (Rle_lt_trans _ (Rabs ((f x' - f x) / (x' - x) - l) + Rabs l)).
      + apply (Rabs_triang ((f x' - f x) / (x' - x) - l) l).
      + apply Rplus_lt_compat_l.
        exact Hf1. }

    (* 计算 |f(x')-f(x)| = |x'-x| * |(f(x')-f(x))/(x'-x)| *)
    replace (f x' - f x) with ((x' - x) * ((f x' - f x) / (x' - x))).
    2: { field. lra. }

    rewrite Rabs_mult.

    (* |x'-x| * |(f(x')-f(x))/(x'-x)| <= |x'-x| * (|l|+1) < eps *)
    apply (Rle_lt_trans _ (Rabs (x' - x) * (Rabs l + 1)) eps).
    + apply Rmult_le_compat_l.
      * exact Hbound.
      * apply Rabs_pos.
    + (* 证明 |x'-x| * (|l|+1) < eps *)
      assert (Hlt: Rabs (x' - x) * (Rabs l + 1) < (eps / (Rabs l + 1)) * (Rabs l + 1)).
      { apply Rmult_lt_compat_r.
        - assert (H: Rabs l + 1 > 0) by lra. exact H.
        - exact Hx2. }
      assert (Hrw: (eps / (Rabs l + 1)) * (Rabs l + 1) = eps).
      { unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l.
        - rewrite Rmult_1_r. reflexivity.
        - assert (H: Rabs l + 1 > 0) by lra.
          apply Rgt_not_eq. exact H. }
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
