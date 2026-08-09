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

  destruct (Hl 1 (Rlt_0_1)) as [delta1 H1].
  destruct delta1 as [delta1 Hdelta1_pos]. simpl in H1.

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
  - rewrite Heq.
    replace (f x - f x) with 0 by lra.
    rewrite Rabs_R0. exact Heps.

  - assert (Hh: x' - x <> 0) by lra.
    assert (Hx1: Rabs (x' - x) < delta1).
    { eapply Rlt_le_trans; [exact Hx' | apply Rmin_l]. }
    assert (Hx2: Rabs (x' - x) < eps / (Rabs l + 1)).
    { eapply Rlt_le_trans; [exact Hx' | apply Rmin_r]. }

    (* 由可微性 *)
    assert (Hf1: Rabs ((f x' - f x) / (x' - x) - l) < 1).
    { replace (Rabs ((f x' - f x) / (x' - x) - l) < 1) with
        (Rabs ((f (x + (x' - x)) - f x) / (x' - x) - l) < 1).
      - apply (H1 (x' - x) Hh Hx1).
      - repeat f_equal; lra. }

    (* 证明 |(f(x')-f x)/(x'-x)| <= |l| + 1 *)
    (* 证明 |(f(x')-f x)/(x'-x)| <= |l| + 1 *)
    assert (Htri: Rabs (((f x' - f x) / (x' - x) - l) + l) <= Rabs ((f x' - f x) / (x' - x) - l) + Rabs l).
    { apply Rabs_triang. }
    assert (Hbound: Rabs ((f x' - f x) / (x' - x)) <= Rabs l + 1).
    { unfold Rle. left.
      replace (Rabs ((f x' - f x) / (x' - x))) with (Rabs ((f x' - f x) / (x' - x) - l + l)).
      2: { repeat f_equal; lra. }
      apply (Rle_lt_trans _ _ _ Htri).
      replace (Rabs l + 1) with (1 + Rabs l).
      2: { rewrite Rplus_comm. reflexivity. }
      apply (Rplus_lt_compat_r _ _ _ Hf1). }

    (* 计算 |f(x')-f(x)| = |x'-x| * |(f(x')-f(x))/(x'-x)| *)
    replace (f x' - f x) with ((x' - x) * ((f x' - f x) / (x' - x))).
    2: { field. lra. }

    rewrite Rabs_mult.

    apply (Rle_lt_trans _ (Rabs (x' - x) * (Rabs l + 1)) eps).
    + apply Rmult_le_compat_l.
      * exact Hbound.
      * apply Rabs_pos.
    + assert (Hlt: Rabs (x' - x) * (Rabs l + 1) < (eps / (Rabs l + 1)) * (Rabs l + 1)).
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

(* ============================================================ *)
(* 微分法则：可加、可乘、倒数                                      *)
(* ============================================================ *)

(* 导数存在性：f 在 x 点可微且导数为 l *)
Definition derivable_at (f : R -> R) (x l : R) : Prop :=
  derivable_pt_lim f x l.

(* 加法法则：(f + g)' = f' + g' *)
Theorem derivable_plus : forall (f g : R -> R) (x lf lg : R),
  derivable_at f x lf ->
  derivable_at g x lg ->
  derivable_at (fun z => f z + g z) x (lf + lg).
Proof.
  intros f g x lf lg Hf Hg.
  unfold derivable_at in *.
  intros eps Heps.
  destruct (Hf eps Heps) as [df [Hdf_pos Hf_eps]].
  destruct (Hg eps Heps) as [dg [Hdg_pos Hg_eps]].
  exists (Rmin df dg).
  split.
  { apply Rmin_pos; [exact Hdf_pos | exact Hdg_pos]. }
  intros h Hh_lt Hh_neq.
  unfold Rminus.
  replace ((f (x + h) + g (x + h) - (f x + g x)) / h) with
    ((f (x + h) - f x) / h + (g (x + h) - g x) / h).
  2: { field. lra. }
  replace (lf + lg) with (lf + lg) by reflexivity.
  apply Rle_lt_trans with
    (Rabs ((f (x + h) - f x) / h - lf) + Rabs ((g (x + h) - g x) / h - lg)).
  - rewrite Rabs_triang.
    right. reflexivity.
  - apply Rplus_lt_compat.
    + apply Hf_eps.
      * lra.
      * exact Hh_neq.
    + apply Hg_eps.
      * lra.
      * exact Hh_neq.
Qed.

(* 乘法法则：(fg)' = f'g + fg' *)
Theorem derivable_mult : forall (f g : R -> R) (x lf lg : R),
  derivable_at f x lf ->
  derivable_at g x lg ->
  derivable_at (fun z => f z * g z) x (lf * g x + f x * lg).
Proof.
  intros f g x lf lg Hf Hg.
  unfold derivable_at in *.
  intros eps Heps.

  (* 利用可微 => 连续 *)
  assert (Hf_cont: continuous_at f x).
  { apply (differentiable_continuous f x x (or_introl (refl_equal _)) (ex_intro _ lf Hf)). }

  destruct (Hf eps Heps) as [df [Hdf_pos Hf_eps]].
  destruct (Hg eps Heps) as [dg [Hdg_pos Hg_eps]].

  (* 连续性给出界 *)
  destruct (Hf_cont 1 (Rlt_0_1)) as [df_cont [Hdf_cont_pos Hf_cont_bound]].

  exists (Rmin df (Rmin dg df_cont)).
  split.
  { apply Rmin_pos.
    - exact Hdf_pos.
    - apply Rmin_pos; [exact Hdg_pos | exact Hdf_cont_pos]. }

  intros h Hh_lt Hh_neq.
  (* 代数变换 *)
  replace ((f (x + h) * g (x + h) - f x * g x) / h) with
    ((f (x + h) - f x) / h * g (x + h) + f x * ((g (x + h) - g x) / h)).
  2: { field. lra. }

  apply Rle_lt_trans with
    (Rabs ((f (x + h) - f x) / h * g (x + h) + f x * ((g (x + h) - g x) / h) - (lf * g x + f x * lg))).
Admitted.

(* 倒数法则：(1/g)' = -g'/g^2 *)
Theorem derivable_inv : forall (g : R -> R) (x lg : R),
  derivable_at g x lg ->
  g x <> 0 ->
  derivable_at (fun z => / g z) x (- lg / (g x * g x)).
Admitted.

(* 推论：区间上可微 => 区间上每点连续 *)
Theorem differentiable_continuous_on_interval : forall (f : R -> R) (a b : R),
  (forall x, in_interval a b x -> differentiable_at f x) ->
  forall x, in_interval a b x -> continuous_at f x.
Proof.
  intros f a b Hdiff x' Hx'.
  apply (differentiable_continuous f a b x' Hx' (Hdiff x' Hx')).
Admitted.
