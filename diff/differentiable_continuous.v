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
  destruct Hdiff as (l & Hl).

  destruct (Hl 1 (Rlt_0_1)) as (delta1 & H1).
  destruct delta1 as (delta1 & Hdelta1_pos). simpl in H1.

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
    assert (Heq_div: (f x' - f x) / (x' - x) = (f x' - f x) / (x' - x) - l + l) by lra.
    assert (Hbound: Rabs ((f x' - f x) / (x' - x)) <= Rabs l + 1).
    { unfold Rle. left.
      assert (Htri: Rabs (((f x' - f x) / (x' - x) - l) + l) <= Rabs ((f x' - f x) / (x' - x) - l) + Rabs l).
      { apply Rabs_triang. }
      assert (Hlt: Rabs ((f x' - f x) / (x' - x) - l) + Rabs l < Rabs l + 1).
      { assert (Hlt_raw: Rabs ((f x' - f x) / (x' - x) - l) + Rabs l < 1 + Rabs l).
        { apply (Rplus_lt_compat_r _ _ _ Hf1). }
        assert (Hcomm: 1 + Rabs l = Rabs l + 1) by (rewrite Rplus_comm; reflexivity).
        destruct Hcomm.
        exact Hlt_raw. }
      assert (Hchain: Rabs ((f x' - f x) / (x' - x) - l + l) < Rabs l + 1).
      { apply (Rle_lt_trans _ _ _ Htri Hlt). }
      replace ((f x' - f x) / (x' - x) - l + l) with ((f x' - f x) / (x' - x)) in Hchain by lra.
      exact Hchain. }

    (* 计算 |f(x')-f(x)| = |x'-x| * |(f(x')-f(x))/(x'-x)| *)
    replace (f x' - f x) with ((x' - x) * ((f x' - f x) / (x' - x))).
    2: { field. lra. }

    rewrite Rabs_mult.

    apply (Rle_lt_trans _ (Rabs (x' - x) * (Rabs l + 1)) eps).
    + apply Rmult_le_compat_l.
      * apply Rabs_pos.
      * exact Hbound.
    + assert (Hlt: Rabs (x' - x) * (Rabs l + 1) < (eps / (Rabs l + 1)) * (Rabs l + 1)).
      { apply Rmult_lt_compat_r.
        - assert (H: 0 <= Rabs l) by apply Rabs_pos.
          assert (H': Rabs l + 1 > 0) by lra.
          exact H'.
        - exact Hx2. }
      assert (Hrw: (eps / (Rabs l + 1)) * (Rabs l + 1) = eps).
      { unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l.
        - rewrite Rmult_1_r. reflexivity.
        - assert (H: 0 <= Rabs l) by apply Rabs_pos.
          assert (H': Rabs l + 1 > 0) by lra.
          apply Rgt_not_eq. exact H'. }
      rewrite Hrw in Hlt.
      exact Hlt.
Qed.

(* ============================================================ *)
(* 微分法则：可加、可乘、复合、倒数                                *)
(* ============================================================ *)

(* 导数存在性 *)
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
  assert (Heps2 : 0 < eps / 2).
  { apply Rlt_div_l.
    - lra.
    - exact Heps.
  }
  destruct (Hf (eps / 2) Heps2) as [df Hf_eps].
  destruct (Hg (eps / 2) Heps2) as [dg Hg_eps].
  destruct df as [df_val df_pos].
  destruct dg as [dg_val dg_pos].
  assert (Hmin_pos : 0 < Rmin df_val dg_val).
  { apply (Rmin_case df_val dg_val (fun r => 0 < r)).
    - exact df_pos.
    - exact dg_pos.
  }
  exists {| pos := Rmin df_val dg_val; cond_pos := Hmin_pos |}.
  simpl.
  intros h Hh_lt Hh_neq.
  replace ((f (x + h) + g (x + h) - (f x + g x)) / h - (lf + lg))
    with (((f (x + h) - f x) / h - lf) + ((g (x + h) - g x) / h - lg))
    by (field; lra).
  apply Rle_lt_trans with (Rabs ((f (x + h) - f x) / h - lf) + Rabs ((g (x + h) - g x) / h - lg)).
  - apply Rabs_triang.
  - apply (Rplus_lt_compat _ _ _ _ (Hf_eps _ _ Hh_lt Hh_neq) (Hg_eps _ _ Hh_lt Hh_neq)).
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

  (* 利用可微 => 连续，得到 f 的有界性 *)
  assert (Hf_cont: continuous_at f x).
  { apply (differentiable_continuous f x x (or_introl (refl_equal _)) (ex_intro _ lf Hf)). }

  destruct (Hf eps Heps) as [df Hf_eps].
  destruct (Hg eps Heps) as [dg Hg_eps].
  destruct df as [df_val df_pos].
  destruct dg as [dg_val dg_pos].
  destruct (Hf_cont 1 (Rlt_0_1)) as [df_cont Hf_cont_bound].
  destruct df_cont as [df_cont_val df_cont_pos].

  assert (Hmin_pos : 0 < Rmin df_val (Rmin dg_val df_cont_val)).
  { apply (Rmin_case df_val (Rmin dg_val df_cont_val) (fun r => 0 < r)).
    - exact df_pos.
    - apply (Rmin_case dg_val df_cont_val (fun r => 0 < r)).
      + exact dg_pos.
      + exact df_cont_pos.
  }
  exists (exist _ (Rmin df_val (Rmin dg_val df_cont_val)) Hmin_pos).
  simpl.
  intros h Hh_lt Hh_neq.

  (* 代数变换：(fg)(x+h) - (fg)(x) = (f(x+h)-f(x))g(x+h) + f(x)(g(x+h)-g(x)) *)
  replace ((f (x + h) * g (x + h) - f x * g x) / h) with
    ((f (x + h) - f x) / h * g (x + h) + f x * ((g (x + h) - g x) / h)).
  2: { field. lra. }

  (* 目标：表达式的值在 lf*g(x) + f(x)*lg 的 eps 范围内 *)
  (* 分解为两部分：A = (f(x+h)-f(x))/h * g(x+h) - lf*g(x) *)
  (*              B = f(x) * ((g(x+h)-g(x))/h - lg) *)
  (* A = (f(x+h)-f(x))/h * g(x+h) - lf*g(x+h) + lf*g(x+h) - lf*g(x) *)
  (*   = g(x+h) * ((f(x+h)-f(x))/h - lf) + lf * (g(x+h) - g(x)) *)

  (* 使用三角不等式 *)
  apply Rle_lt_trans with
    (Rabs (g (x + h) * ((f (x + h) - f x) / h - lf) + lf * (g (x + h) - g x))
     + Rabs (f x * ((g (x + h) - g x) / h - lg))).
Admitted.

(* 链式法则（复合函数）：(g ∘ f)'(x) = g'(f(x)) · f'(x) *)
Theorem derivable_comp : forall (f g : R -> R) (x lf lg : R),
  derivable_at f x lf ->
  derivable_at g (f x) lg ->
  derivable_at (fun z => g (f z)) x (lg * lf).
Proof.
  intros f g x lf lg Hf Hg.
  unfold derivable_at in *.
  intros eps Heps.

  (* 首先，由 g 在 f(x) 可微，得到 g 在 f(x) 的导数定义 *)
  destruct (Hg eps Heps) as [dg_pos Hg_eps].
  destruct dg_pos as [dg Hg_pos].

  (* 由 f 在 x 可微，且 f 连续，f 在 x 附近有界 *)
  assert (Hf_cont: continuous_at f x).
  { apply (differentiable_continuous f x x (or_introl (refl_equal _)) (ex_intro _ lf Hf)). }

  (* 由连续性，存在 delta1 > 0 使得 |x' - x| < delta1 => |f(x') - f(x)| < dg *)
  destruct (Hf_cont dg Hf_cont_bound) as [df_cont Hf_cont_bound'].
  destruct df_cont as [df_cont_val df_cont_pos].
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
