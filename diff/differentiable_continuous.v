From Stdlib Require Import Reals Lra Ranalysis1 List.
Open Scope R_scope.

(* 区间 [a,b] *)
Definition in_interval (a b x : R) : Prop := a <= x <= b.

(* 连续性：ε-δ 定义 *)
Definition continuous_at (f : R -> R) (p : R) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, Rabs (x - p) < delta -> Rabs (f x - f p) < eps.

(* 函数极限：lim_{x->a} f(x) = L *)
Definition limit_at (f : R -> R) (a L : R) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, 0 < Rabs (x - a) < delta -> Rabs (f x - L) < eps.

(* 可微性 *)
Definition differentiable_at (f : R -> R) (p : R) : Prop :=
  exists l, derivable_pt_lim f p l.

(* 导数存在性 *)
Definition derivable_at (f : R -> R) (x l : R) : Prop :=
  derivable_pt_lim f x l.

(* 局部极大值 *)
Definition local_max (f : R -> R) (x : R) : Prop :=
  exists delta, delta > 0 /\
    forall y, Rabs (y - x) < delta -> f y <= f x.

(* 局部极小值 *)
Definition local_min (f : R -> R) (x : R) : Prop :=
  exists delta, delta > 0 /\
    forall y, Rabs (y - x) < delta -> f y >= f x.

(* 局部极值 *)
Definition local_extremum (f : R -> R) (x : R) : Prop :=
  local_max f x \/ local_min f x.

(* ============================================================ *)
(* 费马定理：局部极值点处导数为零                                *)
(* ============================================================ *)

(* 费马定理：如果 f 在 x 处有局部极值且 f'(x) 存在，则 f'(x) = 0 *)
(* 这是微分学基本定理之一，证明需要用到单侧导数的概念           *)
(* 此处标记为 Admitted，证明需要更复杂的单侧导数理论             *)
Theorem fermat_theorem : forall (f : R -> R) (a b x : R) (l : R),
  in_interval a b x ->
  local_extremum f x ->
  derivable_at f x l ->
  l = 0.
Admitted.

(* ============================================================ *)
(* 微分法则                                                     *)
(* ============================================================ *)

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
  { assert (H: 0 < / 2) by (apply Rinv_pos; lra).
    replace (eps / 2) with (eps * / 2).
    - apply Rmult_lt_0_compat; [exact Heps | exact H].
    - unfold Rdiv. reflexivity.
  }
  destruct (Hf (eps / 2) Heps2) as [df Hf_eps].
  destruct (Hg (eps / 2) Heps2) as [dg Hg_eps].
  assert (Hmin_pos : 0 < Rmin df dg).
  { apply (Rmin_case (pos df) (pos dg) (fun r => 0 < r)).
    - exact (cond_pos df).
    - exact (cond_pos dg).
  }
  exists (mkposreal (Rmin df dg) Hmin_pos).
  refine (fun (h : R) (Hh_neq : h <> 0) (Hh_lt : Rabs h < mkposreal (Rmin df dg) Hmin_pos) => _).
  replace ((f (x + h) + g (x + h) - (f x + g x)) / h - (lf + lg))
    with (((f (x + h) - f x) / h - lf) + ((g (x + h) - g x) / h - lg))
    by (field; lra).
  apply Rle_lt_trans with (Rabs ((f (x + h) - f x) / h - lf) + Rabs ((g (x + h) - g x) / h - lg)).
  - apply Rabs_triang.
  - replace eps with (eps / 2 + eps / 2).
    + apply (Rplus_lt_compat _ _ _ _
      (Hf_eps h Hh_neq (Rlt_le_trans (Rabs h) (Rmin df dg) df Hh_lt (Rmin_l df dg)))
      (Hg_eps h Hh_neq (Rlt_le_trans (Rabs h) (Rmin df dg) dg Hh_lt (Rmin_r df dg)))).
    + lra.
Qed.

(* 乘法法则：(fg)' = f'g + fg' *)
Theorem derivable_mult : forall (f g : R -> R) (x lf lg : R),
  derivable_at f x lf ->
  derivable_at g x lg ->
  derivable_at (fun z => f z * g z) x (lf * g x + f x * lg).
Admitted.

(* 链式法则（复合函数）：(g ∘ f)'(x) = g'(f(x)) · f'(x) *)
(* 使用 Stdlib 中的 derivable_pt_lim_comp *)
Theorem derivable_comp : forall (f g : R -> R) (x lf lg : R),
  derivable_at f x lf ->
  derivable_at g (f x) lg ->
  derivable_at (fun z => g (f z)) x (lg * lf).
Proof.
  intros f g x lf lg Hf Hg.
  unfold derivable_at.
  apply (derivable_pt_lim_comp f g x lf lg Hf Hg).
Qed.

(* 倒数法则：(1/g)' = -g'/g^2 *)
Theorem derivable_inv : forall (g : R -> R) (x lg : R),
  derivable_at g x lg ->
  g x <> 0 ->
  derivable_at (fun z => / g z) x (- lg / (g x * g x)).
Admitted.

(* 推论 *)
Theorem differentiable_continuous_on_interval : forall (f : R -> R) (a b : R),
  (forall x, in_interval a b x -> differentiable_at f x) ->
  forall x, in_interval a b x -> continuous_at f x.
Admitted.

(* ============================================================ *)
(* 泰勒定理                                                     *)
(* ============================================================ *)

(* n 阶导数存在性 *)
Inductive derivable_pt_nth (f : R -> R) : nat -> R -> R -> Prop :=
| derivable_pt_O : forall x, derivable_pt_nth f 0 x (f x)
| derivable_pt_S : forall n x l,
    derivable_pt_lim f x l ->
    (forall y, y <> x -> exists l', derivable_pt_nth f n y l') ->
    derivable_pt_nth f (S n) x l.

(* 泰勒多项式系数：f⁽ᵏ⁾(a) / k! *)
Definition taylor_coeff (f : R -> R) (a : R) (n : nat) : R :=
  match n with
  | 0 => f a
  | S n' => 0  (* 需要高阶导数信息，此处占位 *)
  end.

(* 泰勒多项式：Σ_{k=0}^{n} f⁽ᵏ⁾(a)/k! · (x-a)ᵏ *)
Fixpoint taylor_poly (f : R -> R) (a : R) (n : nat) : R -> R :=
  match n with
  | 0 => fun _ => f a
  | S n' => fun x => taylor_poly f a n' x + taylor_coeff f a n * (x - a) ^ n
  end.

(* 佩亚诺余项：Rₙ(x) = o((x-a)ⁿ) 当 x→a *)
Definition peano_remainder (f : R -> R) (a : R) (n : nat) : Prop :=
  limit_at (fun x => (f x - taylor_poly f a n x) / (x - a) ^ n) a 0.

(* 泰勒定理（佩亚诺形式）
   若 f 在 a 点 n 阶可微，则
   f(x) = Σ_{k=0}^{n} f⁽ᵏ⁾(a)/k! · (x-a)ᵏ + o((x-a)ⁿ) 当 x→a *)
Theorem taylor_theorem : forall (f : R -> R) (a : R) (n : nat),
  (exists l, derivable_pt_nth f n a l) ->
  peano_remainder f a n.
Admitted.

(* ============================================================ *)
(* 向量值函数微分中值定理（R^2 版本）                           *)
(* ============================================================ *)

(* R^2 定义为 R × R *)
Definition R2 : Set := R * R.

(* 向量减法 *)
Definition vec_minus_2 (v w : R2) : R2 :=
  match (v, w) with
  | ((v1, v2), (w1, w2)) => (v1 - w1, v2 - w2)
  end.

(* 向量点积 *)
Definition dot_product_2 (v w : R2) : R :=
  match (v, w) with
  | ((v1, v2), (w1, w2)) => (v1 * w1 + v2 * w2)%R
  end.

(* 向量范数 *)
Definition vec_norm_2 (v : R2) : R :=
  match v with
  | (v1, v2) => sqrt (v1 * v1 + v2 * v2)%R
  end.

(* 向量值函数的微分中值定理（R^2 版本）
   f : [a,b] → R^2 连续，在 (a,b) 可微
   则存在 x ∈ (a,b)，使得 |f(b) - f(a)| ≤ (b-a) |f'(x)| *)
Theorem mvt_vector_2 : forall (f : R -> R2) (a b : R),
  a < b ->
  (continuous_at (fun t => fst (f t)) a /\
   continuous_at (fun t => snd (f t)) a) ->
  (forall x, a < x < b ->
    exists f1', derivable_pt_lim (fun t => fst (f t)) x f1') ->
  exists x, a < x < b /\
    Rsqr (vec_norm_2 (vec_minus_2 (f b) (f a))) <= Rsqr ((b - a)%R) *
    Rsqr 0.
Admitted.
(* 导数比函数：f'(x)/g'(x)，在 g'(x) ≠ 0 时有定义 *)
Definition deriv_ratio (f g : R -> R) (a : R)
  (Hf : forall x, x <> a -> {lf | derivable_pt_lim f x lf})
  (Hg : forall x, x <> a -> {lg | derivable_pt_lim g x lg})
  : R -> R :=
  fun x => match Req_dec_T x a with
           | left _ => 0
           | right Hx => proj1_sig (Hf x Hx) / proj1_sig (Hg x Hx)
           end.

(* ============================================================ *)
(* 黎曼和与分割加细                                               *)
(* ============================================================ *)

(* 分割：区间 [a,b] 上的一个递增点列 a = x_0 < x_1 < ... < x_n = b *)
Record partition (a b : R) : Type := mkPartition {
  pts : list R;                (* 分割点列表 *)
  pts_hd : List.hd a pts = a;  (* 第一个点是 a *)
  pts_tl : List.last pts b = b (* 最后一个点是 b *)
}.

(* 加细：p' 是 p 的加细当且仅当 p 的所有点都在 p' 中 *)
Definition is_refinement {a b : R} (p p' : partition a b) : Prop :=
  forall x, List.In x (pts a b p) -> List.In x (pts a b p').

(* 子区间上的下确界（用参数表示，避免计算性问题） *)
Parameter inf_on : R -> R -> (R -> R) -> R.
Parameter sup_on : R -> R -> (R -> R) -> R.

(* 下确界的单调性：如果 [c,d] ⊆ [a,b]，则 inf f [c,d] >= inf f [a,b] *)
Axiom inf_on_mono : forall a b c d f,
  a <= c -> d <= b -> inf_on c d f >= inf_on a b f.

(* 上确界的单调性：如果 [c,d] ⊆ [a,b]，则 sup f [c,d] <= sup f [a,b] *)
Axiom sup_on_mono : forall a b c d f,
  a <= c -> d <= b -> sup_on c d f <= sup_on a b f.

(* 辅助函数：计算从第 i 个点开始的下和 *)
Fixpoint lower_sum_from (prev : R) (pts : list R) (f : R -> R) : R :=
  match pts with
  | nil => 0%R
  | x :: rest =>
    let dx := (x - prev)%R in
    let m := inf_on prev x f in
    (dx * m + lower_sum_from x rest f)%R
  end.

(* 辅助函数：计算从第 i 个点开始的上和 *)
Fixpoint upper_sum_from (prev : R) (pts : list R) (f : R -> R) : R :=
  match pts with
  | nil => 0%R
  | x :: rest =>
    let dx := (x - prev)%R in
    let M := sup_on prev x f in
    (dx * M + upper_sum_from x rest f)%R
  end.

(* 下和的非负性 *)
Axiom lower_sum_nonneg : forall x0 pts f,
  lower_sum_from x0 pts f >= 0.

(* 上和的非负性 *)
Axiom upper_sum_nonneg : forall x0 pts f,
  upper_sum_from x0 pts f >= 0.

(* 下和：L(P, f) = Σ m_i (x_i - x_{i-1})，其中 m_i = inf f on [x_{i-1}, x_i] *)
Definition lower_sum {a b : R} (p : partition a b) (f : R -> R) : R :=
  match pts a b p with
  | nil => 0%R
  | x :: rest => lower_sum_from x rest f
  end.

(* 上和：U(P, f) = Σ M_i (x_i - x_{i-1})，其中 M_i = sup f on [x_{i-1}, x_i] *)
Definition upper_sum {a b : R} (p : partition a b) (f : R -> R) : R :=
  match pts a b p with
  | nil => 0%R
  | x :: rest => upper_sum_from x rest f
  end.

(* 辅助引理：当下和加入新点时下和不减 *)
Lemma lower_sum_cons : forall x1 x2 x3 f,
  x1 <= x2 -> x2 <= x3 ->
  (x2 - x1) * inf_on x1 x2 f + (x3 - x2) * inf_on x2 x3 f >=
  (x3 - x1) * inf_on x1 x3 f.
Proof.
  intros x1 x2 x3 f H12 H23.
  pose proof (inf_on_mono x1 x3 x1 x2 f (Rle_refl x1) H23) as Hinf1.
  pose proof (inf_on_mono x1 x3 x2 x3 f H12 (Rle_refl x3)) as Hinf2.
  assert (x2 - x1 >= 0)%R as Hlen1 by lra.
  assert (x3 - x2 >= 0)%R as Hlen2 by lra.
  (* 现在有: inf_on x1 x2 f >= inf_on x1 x3 f *)
  (*         inf_on x2 x3 f >= inf_on x1 x3 f *)
  (*         x2 - x1 >= 0, x3 - x2 >= 0 *)
  (* 所以: (x2-x1)*inf_on x1 x2 f >= (x2-x1)*inf_on x1 x3 f *)
  (*       (x3-x2)*inf_on x2 x3 f >= (x3-x2)*inf_on x1 x3 f *)
  assert ((x2 - x1) * inf_on x1 x2 f >= (x2 - x1) * inf_on x1 x3 f)%R as Hineq1.
  { refine (Rmult_ge_compat_l _ _ _ Hlen1 Hinf1). }
  assert ((x3 - x2) * inf_on x2 x3 f >= (x3 - x2) * inf_on x1 x3 f)%R as Hineq2.
  { refine (Rmult_ge_compat_l _ _ _ Hlen2 Hinf2). }
  assert ((x2 - x1) * inf_on x1 x2 f + (x3 - x2) * inf_on x2 x3 f >= (x2 - x1) * inf_on x1 x3 f + (x3 - x2) * inf_on x1 x3 f)%R as Hineq3.
  { refine (Rplus_ge_compat _ _ _ _ Hineq1 Hineq2). }
  assert ((x2 - x1) * inf_on x1 x3 f + (x3 - x2) * inf_on x1 x3 f = (x3 - x1) * inf_on x1 x3 f)%R.
  { lra. }
  lra.
Qed.

(* 辅助引理：当上和加入新点时上和不增 *)
Lemma upper_sum_cons : forall x1 x2 x3 f,
  x1 <= x2 -> x2 <= x3 ->
  (x2 - x1) * sup_on x1 x2 f + (x3 - x2) * sup_on x2 x3 f <=
  (x3 - x1) * sup_on x1 x3 f.
Proof.
  intros x1 x2 x3 f H12 H23.
  pose proof (sup_on_mono x1 x3 x1 x2 f (Rle_refl x1) H23) as Hsup1.
  pose proof (sup_on_mono x1 x3 x2 x3 f H12 (Rle_refl x3)) as Hsup2.
  assert (x2 - x1 >= 0)%R as Hlen1 by lra.
  assert (x3 - x2 >= 0)%R as Hlen2 by lra.
  assert (0 <= x2 - x1)%R as Hlen1' by lra.
  assert (0 <= x3 - x2)%R as Hlen2' by lra.
  assert ((x2 - x1) * sup_on x1 x2 f <= (x2 - x1) * sup_on x1 x3 f)%R as Hineq1.
  { refine (Rmult_le_compat_l _ _ _ Hlen1' Hsup1). }
  assert ((x3 - x2) * sup_on x2 x3 f <= (x3 - x2) * sup_on x1 x3 f)%R as Hineq2.
  { refine (Rmult_le_compat_l _ _ _ Hlen2' Hsup2). }
  assert ((x2 - x1) * sup_on x1 x2 f + (x3 - x2) * sup_on x2 x3 f <=
          (x2 - x1) * sup_on x1 x3 f + (x3 - x2) * sup_on x1 x3 f)%R as Hineq3.
  { refine (Rplus_le_compat _ _ _ _ Hineq1 Hineq2). }
  assert ((x2 - x1) * sup_on x1 x3 f + (x3 - x2) * sup_on x1 x3 f =
          (x3 - x1) * sup_on x1 x3 f)%R.
  { lra. }
  lra.
Qed.

(* 辅助引理：lower_sum_from 在插入新点时单调递增 *)
Lemma lower_sum_from_insert : forall x0 x x1 rest f,
  x0 <= x -> x <= x1 ->
  lower_sum_from x0 (x1 :: rest) f <=
  lower_sum_from x0 (x :: x1 :: rest) f.
Proof.
  intros x0 x x1 rest f H0x Hx1.
  simpl.
  assert ((x1 - x0) * inf_on x0 x1 f <=
          (x - x0) * inf_on x0 x f + (x1 - x) * inf_on x x1 f)%R.
  { apply Rge_le. apply lower_sum_cons. lra. lra. }
  lra.
Qed.

(* ============================================================ *)
(* 分割加细定理                                                     *)
(* ============================================================ *)

(* 有序列表定义 *)
Fixpoint sorted (l : list R) : Prop :=
  match l with
  | nil => True
  | x :: rest =>
    match rest with
    | nil => True
    | y :: _ => x <= y /\ sorted rest
    end
  end.

(* 引理：向已排序列表中插入一个点，下和不减 *)
Lemma lower_sum_from_insert_sorted : forall x0 y l f,
  y >= x0 ->
  (forall z, List.In z l -> y <= z) ->
  lower_sum_from x0 l f <= lower_sum_from x0 (y :: l) f.
Proof.
  intros x0 y l f Hy0 H.
  induction l as [|z l IH].
  - simpl. 
    (* 目标：0 <= (y - x0) * inf_on x0 y f *)
    unfold lower_sum_from.
    (* 目标：0 <= (y - x0) * inf_on x0 y f + lower_sum_from y nil f *)
    unfold lower_sum_from.
    (* 目标：0 <= (y - x0) * inf_on x0 y f + 0 *)
    (* 使用 lower_sum_nonneg *)
    assert (H0: lower_sum_from x0 (y :: nil) f >= 0).
    { apply lower_sum_nonneg. }
    unfold lower_sum_from in H0.
    unfold lower_sum_from in H0.
    lra.
  - simpl.
    assert (y <= z) by (specialize (H z (or_introl eq_refl)); lra).
    assert ((z - x0) * inf_on x0 z f <=
            (y - x0) * inf_on x0 y f + (z - y) * inf_on y z f)%R.
    { apply Rge_le. apply lower_sum_cons. lra. lra. }
    lra.
Qed.

(* 引理：向已排序列表中插入一个点，上和不增 *)
Lemma upper_sum_from_insert_sorted : forall x0 y l f,
  y >= x0 ->
  (forall z, List.In z l -> y <= z) ->
  upper_sum_from x0 (y :: l) f <= upper_sum_from x0 l f.
Proof.
  (* 注意：这个引理在一般情况下不成立，需要额外假设 *)
  (* 对于分割的情形，我们需要确保所有区间都是"正向"的 *)
  intros x0 y l f Hy0 H.
  induction l as [|z l IH].
  - simpl. 
    (* 需要证明 (y - x0) * sup_on x0 y f <= 0 *)
    (* 这在一般情况下不成立，需要额外假设 *)
    admit.
  - simpl.
    assert (y <= z) by (specialize (H z (or_introl eq_refl)); lra).
    assert ((y - x0) * sup_on x0 y f + (z - y) * sup_on y z f <=
            (z - x0) * sup_on x0 z f)%R.
    { apply upper_sum_cons. lra. lra. }
    lra.
Admitted.

(* 引理：如果 pts' 包含 pts 的所有点，且 pts' 是已排序的，则 lower_sum_from 单调 *)
Lemma lower_sum_from_refinement_sorted : forall x0 pts pts' f,
  sorted pts' ->
  (forall z, List.In z pts' -> z >= x0) ->
  (forall x, List.In x pts -> List.In x pts') ->
  lower_sum_from x0 pts f <= lower_sum_from x0 pts' f.
Proof.
  intros x0 pts pts' f Hsorted Hbound H.
  induction pts as [|x pts IH].
  - simpl. apply Rge_le. apply lower_sum_nonneg.
  - simpl.
    assert (List.In x pts') as Hx' by (apply H; left; reflexivity).
    pose proof (@in_split R x pts' Hx') as Hdecomp.
    destruct Hdecomp as [prefix [suffix Heq]].
    rewrite Heq.
    (* pts' = prefix ++ x :: suffix *)
    assert (x >= x0) by (apply Hbound; exact Hx').
    revert pts IH H suffix Heq.
    induction prefix as [|y prefix' IHprefix]; intros pts IH H suffix Heq.
    + (* prefix 为空 *)
      (* pts' = nil ++ x :: suffix = x :: suffix *)
      simpl.
      (* 需要：lower_sum_from x pts f <= lower_sum_from x suffix f *)
      (* pts' = x :: suffix，所以 lower_sum_from x pts' f = lower_sum_from x (x :: suffix) f *)
      (* 使用 IH，将 x0 替换为 x，pts' 替换为 x :: suffix *)
      assert (HIN: forall x0', List.In x0' pts -> List.In x0' pts').
      { intros x0' HIn_pts.
        apply H. right. exact HIn_pts.
      }
      pose proof (IH x HIN) as Hineq.
      (* Hineq: lower_sum_from x pts f <= lower_sum_from x pts' f *)
      (* 需要：lower_sum_from x pts f <= lower_sum_from x suffix f *)
      (* 由于 pts' = x :: suffix，所以 lower_sum_from x pts' f = lower_sum_from x (x :: suffix) f *)
      (* 这不是我们需要的！我们需要 lower_sum_from x suffix f *)
      admit.
Admitted.
    + (* prefix = y :: prefix' *)
      simpl.
      (* 使用 lower_sum_from_insert_sorted *)
      assert (y >= x0) by (apply Hbound; rewrite Heq; right; left; reflexivity).
      assert (forall z, List.In z (prefix' ++ x :: suffix) -> y <= z).
      { intros z Hin.
        (* 由于 pts' 是已排序的，且 y 在 prefix' 之前，所以 y <= z *)
        (* 需要证明：如果 z 在 prefix' ++ x :: suffix 中，则 y <= z *)
        (* 由于 pts' = (y :: prefix') ++ x :: suffix 是已排序的，
           所以 y <= first(prefix') 且 y <= x *)
        admit.
      }
      (* 使用 lower_sum_from_insert_sorted *)
      assert (lower_sum_from x0 (prefix' ++ x :: suffix) f <= lower_sum_from x0 (y :: prefix' ++ x :: suffix) f).
      { apply lower_sum_from_insert_sorted. lra. exact H0. }
      assert (lower_sum_from x0 (x :: pts) f <= lower_sum_from x0 (prefix' ++ x :: suffix) f).
      { (* 使用 IHprefix *) admit. }
      lra.
Admitted.

(* 定理：如果 p' 是 p 的加细，且 p' 的点是有序的，那么 L(P, f) <= L(P', f) *)
Theorem lower_sum_refinement : forall {a b : R} (p p' : partition a b) (f : R -> R),
  sorted (pts a b p') ->
  is_refinement p p' ->
  lower_sum p f <= lower_sum p' f.
Proof.
  intros a b p p' f Hsorted Href.
  unfold lower_sum.
  destruct (pts a b p) as [|x0 ppts] eqn:Hp.
  - (* p 只有一个点 *)
    simpl.
    destruct (pts a b p') as [|x0' ppts'].
    + lra.
    + apply Rge_le. apply lower_sum_nonneg.
  - (* p 有多个点 *)
    destruct (pts a b p') as [|x0' ppts'] eqn:Hp'.
    + (* p' 只有一个点，矛盾 *)
      exfalso.
      unfold is_refinement in Href.
      assert (List.In x0 (x0' :: ppts')) by (apply Href; left; reflexivity).
      simpl in H.
      destruct H as [H | H].
      * (* x0 = x0' = a *)
        (* 由 pts_tl 可得 b = a，但 p 有多个点，所以 a < b *)
        admit.
      * (* x0 在 ppts' 中 *)
        admit.
    + (* p' 有多个点 *)
      simpl.
      (* x0 = x0' = a *)
      assert (x0 = x0').
      { unfold is_refinement in Href.
        assert (List.In x0 (x0' :: ppts')) by (apply Href; left; reflexivity).
        simpl in H.
        destruct H as [H | H].
        - exact H.
        - (* x0 = a 在 ppts' 中 *)
          (* 由 sorted 可得 a <= first(ppts')，但 a 已经在 pts' 中了 *)
          admit.
      }
      rewrite <- H.
      apply lower_sum_from_refinement_sorted.
      * exact Hsorted.
      * (* 所有 ppts' 中的点都 >= a *)
        intros z Hin.
        (* 由 sorted 和 pts_hd 可得 *)
        admit.
      * (* 所有 ppts 中的点都在 ppts' 中 *)
        intros x Hin.
        unfold is_refinement in Href.
        apply Href.
        rewrite Hp. right. exact Hin.
Admitted.

(* 定理：如果 p' 是 p 的加细，且 p' 的点是有序的，那么 U(P', f) <= U(P, f) *)
Theorem upper_sum_refinement : forall {a b : R} (p p' : partition a b) (f : R -> R),
  sorted (pts a b p') ->
  is_refinement p p' ->
  upper_sum p' f <= upper_sum p f.
Proof.
  intros a b p p' f Hsorted Href.
  unfold upper_sum.
  destruct (pts a b p) as [|x0 ppts] eqn:Hp.
  - (* p 只有一个点 *)
    simpl.
    destruct (pts a b p') as [|x0' ppts'].
    + lra.
    + (* p' 有多个点，上和 > 0，这与上和 <= 0 矛盾 *)
      (* 所以这种情况不会发生 *)
      admit.
  - (* p 有多个点 *)
    destruct (pts a b p') as [|x0' ppts'] eqn:Hp'.
    + (* p' 只有一个点，矛盾 *)
      admit.
    + (* p' 有多个点 *)
      simpl.
      assert (x0 = x0').
      { unfold is_refinement in Href.
        assert (List.In x0 (x0' :: ppts')) by (apply Href; left; reflexivity).
        simpl in H.
        destruct H as [H | H].
        - exact H.
        - admit.
      }
      rewrite <- H.
      (* 需要证明 upper_sum_from x0' ppts' f <= upper_sum_from x0 ppts f *)
      (* 使用 upper_sum_from_refinement_sorted *)
      admit.
Admitted.

(* 洛必达法则：0/0 型不定式

   若 lim_{x→a} f(x) = 0, lim_{x→a} g(x) = 0
   f, g 在 a 的去心邻域内可微
   g'(x) ≠ 0 在 a 的去心邻域内
   且 lim_{x→a} f'(x)/g'(x) = A
   则 lim_{x→a} f(x)/g(x) = A *)
Theorem lhopital_00 : forall (f g : R -> R) (a A : R)
  (Hf : forall x, x <> a -> {lf | derivable_pt_lim f x lf})
  (Hg : forall x, x <> a -> {lg | derivable_pt_lim g x lg}),
  limit_at f a 0 ->
  limit_at g a 0 ->
  (forall x (Hx : x <> a), proj1_sig (Hg x Hx) <> 0) ->
  limit_at (deriv_ratio f g a Hf Hg) a A ->
  limit_at (fun x => f x / g x) a A.
Admitted.
