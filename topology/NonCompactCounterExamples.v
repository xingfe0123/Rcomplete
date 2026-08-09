(*
  ================================================================================
  NonCompactCounterExamples.v — 非紧集上的连续反例函数
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

    10|  定理：设 E ⊆ R 非紧，则
    11|    1) 存在 E 上连续无界的函数
    12|    2) 存在 E 上连续有界但无最大值的函数
    13|    3) 若 E 有不在 E 中的极限点，则存在 E 上连续但不一致连续的函数
    14|
    15|  核心分类：非紧 ⟺ 无界 ∨ (有界但不闭)
    16|  ================================================================================
    17|*)
    18|
    19|From Stdlib Require Import Reals Lra ClassicalEpsilon Psatz.
    20|
    21|Open Scope R_scope.
    22|
    23|(* ================================================================ *)
    24|(*  拓扑定义                                                          *)
    25|(* ================================================================ *)
    26|
    27|Definition is_closed (E : R -> Prop) : Prop :=
    28|  forall a, (forall r, r > 0 -> exists x, E x /\ Rabs (x - a) < r /\ x <> a) -> E a.
    29|
    30|Definition is_bounded (E : R -> Prop) : Prop :=
    31|  exists M, forall x, E x -> Rabs x <= M.
    32|
    33|Definition is_compact (E : R -> Prop) : Prop :=
    34|  is_closed E /\ is_bounded E.
    35|
    36|Definition limit_point (E : R -> Prop) (a : R) : Prop :=
    37|  forall r, r > 0 -> exists x, E x /\ Rabs (x - a) < r /\ x <> a.
    38|
    39|Definition has_limit_point_outside (E : R -> Prop) : Prop :=
    40|  exists a, ~ E a /\ limit_point E a.
    41|
    42|(* ================================================================ *)
    43|(*  函数性质定义                                                      *)
    44|(* ================================================================ *)
    45|
    46|Definition continuous_on_E (E : R -> Prop) (f : R -> R) : Prop :=
    47|  forall x, E x -> forall eps, eps > 0 ->
    48|    exists delta, delta > 0 /\
    49|      forall y, E y -> Rabs (x - y) < delta -> Rabs (f x - f y) < eps.
    50|
    51|Definition bounded_fun_on_E (E : R -> Prop) (f : R -> R) : Prop :=
    52|  exists M, forall x, E x -> Rabs (f x) <= M.
    53|
    54|Definition has_max_on_E (E : R -> Prop) (f : R -> R) : Prop :=
    55|  exists x0, E x0 /\ forall x, E x -> f x <= f x0.
    56|
    57|Definition uniformly_continuous_on_E (E : R -> Prop) (f : R -> R) : Prop :=
    58|  forall eps, eps > 0 ->
    59|    exists delta, delta > 0 /\
    60|      forall x y, E x -> E y -> Rabs (x - y) < delta -> Rabs (f x - f y) < eps.
    61|
    62|(* ================================================================ *)
    63|(*  公理：标准函数性质                                               *)
    64|(* ================================================================ *)
    65|
    66|Axiom Rabs_cont_on : forall E, continuous_on_E E Rabs.
    67|Axiom atan_cont_on : forall E, continuous_on_E E atan.
    68|Axiom atan_bounded_on : forall E, bounded_fun_on_E E atan.
    69|Axiom atan_lt_pi2 : forall x, atan x < PI / 2.
    70|Axiom atan_gt_mpi2 : forall x, atan x > - PI / 2.
    71|Axiom atan_lt : forall x y, x < y -> atan x < atan y.
    72|
    73|Axiom inv_abs_cont : forall E a, ~ E a -> continuous_on_E E (fun x => / Rabs (x - a)).
    74|Axiom inv_1px_cont : forall E a, ~ E a -> continuous_on_E E (fun x => 1 / (1 + Rabs (x - a))).
    75|
    76|(* ================================================================ *)
    77|(*  引理                                                              *)
    78|(* ================================================================ *)
    79|
    80|Lemma not_closed_has_limit_point_outside :
    81|  forall E, ~ is_closed E -> has_limit_point_outside E.
    82|Proof.
    83|  intros E Hnc.
    84|  unfold is_closed in Hnc.
    85|  apply not_all_ex_not in Hnc.
    86|  destruct Hnc as [a Ha].
    87|  apply not_imply_elim in Ha as Hlim.
    88|  apply not_imply_elim2 in Ha as Hna.
    89|  exists a. split. exact Hna. exact Hlim.
    90|Qed.
    91|
    92|(* 无界集上 |x| 无界 *)
    93|Lemma abs_unbounded_on_unbounded :
    94|  forall E, ~ is_bounded E -> ~ bounded_fun_on_E E Rabs.
    95|Proof.
    96|  intros E Hnb Hb.
    97|  unfold bounded_fun_on_E in Hb.
    98|  destruct Hb as [M Hb].
    99|  unfold is_bounded in Hnb.
   100|  assert (Hnb_M : ~ (forall x, E x -> Rabs x <= M)).
   101|  { intro H. apply Hnb. exists M. exact H. }
   102|  apply not_all_ex_not in Hnb_M.
   103|  destruct Hnb_M as [x Hx].
   104|  assert (HxE : E x). { apply not_imply_elim in Hx. exact Hx. }
   105|  assert (HxM : Rabs x > M). { apply not_imply_elim2 in Hx. unfold not in Hx. apply Rnot_le_gt in Hx. exact Hx. }
   106|  specialize (Hb x HxE).
   107|  assert (Hb': Rabs x <= M).
   108|  { assert (Heq: Rabs (Rabs x) = Rabs x). { rewrite Rabs_right. reflexivity. apply Rle_ge. apply Rabs_pos. }
   109|    rewrite Heq in Hb. exact Hb. }
   110|  assert (Habsurd: M < M).
   111|  { apply Rlt_le_trans with (Rabs x). exact HxM. exact Hb'. }
   112|  lra.
   113|Qed.
   114|
   115|(* 有界不闭：1/|x-a| 无界 *)
   116|Lemma inv_abs_unbounded :
   117|  forall E a, is_bounded E -> ~ E a -> limit_point E a ->
   118|    ~ bounded_fun_on_E E (fun x => / Rabs (x - a)).
   119|Proof.
   120|  intros E a Hb Hna Hlim [M Hbnd].
   121|  assert (HM: M + 1 > 0).
   122|  { assert (Hpos: forall x, E x -> 0 <= Rabs (/ Rabs (x - a))).
   123|    { intros x Hx. apply Rabs_pos. }
   124|    unfold limit_point in Hlim.
   125|    edestruct (Hlim 1) as [x [Hx [Hxa Hneq]]].
   126|    - lra.
   127|    - specialize (Hbnd x Hx).
   128|      assert (Hnonneg: 0 <= Rabs (/ Rabs (x - a))) by apply Rabs_pos.
   129|      assert (Hle: 0 <= M).
   130|      { apply Rle_trans with (Rabs (/ Rabs (x - a))). exact Hnonneg. exact Hbnd. }
   131|      psatz.R.
   132|  }
   133|  unfold limit_point in Hlim.
   134|  destruct (Hlim (/ (M + 1))) as [x [Hx [Hxa Hneq]]].
   135|  - apply Rinv_0_lt_compat. lra.
   136|  - specialize (Hbnd x Hx).
   137|    assert (Rinv (Rabs (x - a)) > M + 1).
   138|    { apply Rinv_1_lt_contravar.
   139|      - apply Rmult_lt_0_compat. lra. apply Rabs_pos_lt. exact Hneq.
   140|      - exact Hxa. }
   141|    assert (Rabs (/ Rabs (x - a)) > M + 1).
   142|    { rewrite Rabs_right. lra. apply Rlt_ge. apply Rinv_0_lt_compat. apply Rabs_pos_lt. exact Hneq. }
   143|    assert (Hcontra: M + 1 < M).
   144|    { apply Rlt_le_trans with (Rabs (/ Rabs (x - a))). lra. exact Hbnd. }
   145|    lra.
   146|Qed.
   147|
   148|(* arctan 在无界集上无最大值 *)
   149|Lemma atan_no_max_on_unbounded :
   150|  forall E, ~ is_bounded E -> ~ has_max_on_E E atan.
   151|Proof.
   152|  intros E Hnb [x0 [Hx0 Hmax]].
   153|  specialize (Hmax x0 Hx0).
   154|  unfold is_bounded in Hnb.
   155|  assert (Hnb_x0 : ~ (forall x, E x -> Rabs x <= Rabs x0 + 1)).
   156|  { intro H. apply Hnb. exists (Rabs x0 + 1). exact H. }
   157|  apply not_all_ex_not in Hnb_x0.
   158|  destruct Hnb_x0 as [x Hx].
   159|  assert (HxE : E x). { apply not_imply_elim in Hx. exact Hx. }
   160|  assert (Hxgt : Rabs x > Rabs x0 + 1). { apply not_imply_elim2 in Hx. unfold not in Hx. apply Rnot_le_gt in Hx. exact Hx. }
   161|  specialize (Hmax x HxE).
   162|  assert (x > x0).
   163|  { destruct (Rcase_abs x0).
   164|    - assert (Rabs x > Rabs x0) by lra. unfold Rabs in H. unfold Rabs in Hxgt.
   165|      destruct (Rcase_abs x).
   166|      + lra.
   167|      + lra.
   168|    - assert (Rabs x > Rabs x0) by lra. unfold Rabs in H. unfold Rabs in Hxgt.
   169|      destruct (Rcase_abs x).
   170|      + lra.
   171|      + lra.
   172|  }
   173|  assert (atan x > atan x0).
   174|  { apply atan_lt. exact H. }
   175|  lra.
   176|Qed.
   177|
   178|(* f(x) = 1/(1+|x-a|) 在 E 上无最大值 *)
   179|Lemma inv_1px_no_max :
   180|  forall E a, ~ E a -> limit_point E a ->
   181|    ~ has_max_on_E E (fun x => 1 / (1 + Rabs (x - a))).
   182|Proof.
   183|  intros E a Hna Hlim [x0 [Hx0 Hmax]].
   184|  specialize (Hmax x0 Hx0).
   185|  unfold limit_point in Hlim.
   186|  destruct (Hlim (Rabs (x0 - a) / 2)) as [x [Hx [Hxa Hneq]]].
   187|  - apply Rlt_div_r. lra. apply Rabs_pos_lt. intro H0. subst x0. contradiction.
   188|  - assert (Rabs (x - a) < Rabs (x0 - a)).
   189|    { lra. }
   190|    specialize (Hmax x Hx).
   191|    assert (1 / (1 + Rabs (x - a)) > 1 / (1 + Rabs (x0 - a))).
   192|    { apply Rinv_1_lt_contravar.
   193|      - rewrite Rmult_0_r. apply Rabs_pos_lt. intro H0. subst x. contradiction.
   194|      - lra. }
   195|    lra.
   196|Qed.
   197|
   198|(* 1/|x-a| 不一致连续 *)
   199|Lemma inv_abs_not_uc :
   200|  forall E a, ~ E a -> limit_point E a ->
   201|    ~ uniformly_continuous_on_E E (fun x => / Rabs (x - a)).
   202|Proof.
   203|  intros E a Hna Hlim Huc.
   204|  unfold uniformly_continuous_on_E in Huc.
   205|  specialize (Huc 1) as [delta [Hdelta _]]. lra.
   206|  unfold limit_point in Hlim.
   207|  destruct (Hlim (Rmin (delta / 2) (1 / 2))) as [x [Hx [Hxa Hxneq]]].
   208|  - apply Rmin_case. apply Rlt_div_r. lra. lra. rewrite Rmult_0_r. lra.
   209|  - destruct (Hlim (Rmin (Rabs (x - a) / 2) (1 / 2))) as [y [Hy [Hyx Hyneq]]].
   210|    + apply Rmin_case. apply Rlt_div_r. lra. apply Rabs_pos_lt. exact Hxneq. rewrite Rmult_0_r. lra.
   211|    + assert (Rabs (x - y) < delta).
   212|      { assert (Rabs (x - y) <= Rabs (x - a) + Rabs (y - a)). apply Rabs_triang.
   213|        assert (Rabs (y - a) < Rabs (x - a) / 2). apply (Rlt_le_trans _ _ _ Hyx). apply Rmin_l.
   214|        lra.
   215|      }
   216|      assert (Rabs (/ Rabs(x-a) - / Rabs(y-a)) >= 1).
   217|      { assert (Rabs (y - a) < Rabs (x - a) / 2). apply (Rlt_le_trans _ _ _ Hyx). apply Rmin_l.
   218|        assert (/ Rabs (y - a) >= 2 / Rabs (x - a)).
   219|        { apply Rinv_1_lt_contravar. apply Rmult_lt_0_compat. lra. apply Rabs_pos_lt. exact Hyneq. lra. }
   220|        assert (Rabs (/ Rabs(x-a) - / Rabs(y-a)) >= / Rabs (x - a)).
   221|        { unfold Rminus. rewrite Rabs_Rminus. rewrite Rabs_right. lra. apply Rlt_ge. apply Rinv_0_lt_compat. apply Rabs_pos_lt. exact Hxneq. }
   222|        assert (/ Rabs (x - a) >= 1).
   223|        { apply Rinv_le_var. lra. apply Rabs_pos. lra. }
   224|        lra.
   225|      }
   226|      specialize (Huc delta Hdelta x y Hx Hy H).
   227|      lra.
   228|Qed.
   229|
   230|(* ================================================================ *)
   231|(*  定理 1：非紧 ⟹ 存在连续无界函数                              *)
   232|(* ================================================================ *)
   233|
   234|Theorem thm1_unbounded_continuous :
   235|  forall E, ~ is_compact E ->
   236|    exists f, continuous_on_E E f /\ ~ bounded_fun_on_E E f.
   237|Proof.
   238|  intros E Hnc.
   239|  unfold is_compact in Hnc.
   240|  apply not_and_or in Hnc.
   241|  destruct Hnc as [Hnclosed | Hnbounded].
   242|  - apply not_closed_has_limit_point_outside in Hnclosed as [a [Hna Hlim]].
   243|    exists (fun x => / Rabs (x - a)).
   244|    split.
   245|    + apply inv_abs_cont. exact Hna.
   246|    + assert (Hb : is_bounded E). { tauto. }
   247|      apply inv_abs_unbounded. exact Hb. exact Hna. exact Hlim.
   248|  - exists Rabs.
   249|    split.
   250|    + apply Rabs_cont_on.
   251|    + apply abs_unbounded_on_unbounded. exact Hnbounded.
   252|Qed.
   253|
   254|(* ================================================================ *)
   255|(*  定理 2：非紧 ⟹ 存在连续有界无最大值函数                        *)
   256|(* ================================================================ *)
   257|
   258|Theorem thm2_bounded_no_max :
   259|  forall E, ~ is_compact E ->
   260|    exists f, continuous_on_E E f /\ bounded_fun_on_E E f /\ ~ has_max_on_E E f.
   261|Proof.
   262|  intros E Hnc.
   263|  unfold is_compact in Hnc.
   264|  apply not_and_or in Hnc.
   265|  destruct Hnc as [Hnclosed | Hnbounded].
   266|  - apply not_closed_has_limit_point_outside in Hnclosed as [a [Hna Hlim]].
   267|    exists (fun x => 1 / (1 + Rabs (x - a))).
   268|    split. apply inv_1px_cont. exact Hna.
   269|    split. exists 1. intros x Hx. rewrite Rabs_right. lra. apply Rlt_ge. apply Rinv_0_lt_compat. lra.
   270|    apply inv_1px_no_max. exact Hna. exact Hlim.
   271|  - exists atan.
   272|    split. apply atan_cont_on.
   273|    split. apply atan_bounded_on.
   274|    apply atan_no_max_on_unbounded. exact Hnbounded.
   275|Qed.
   276|
   277|(* ================================================================ *)
   278|(*  定理 3：非紧 + 有外部极限点 ⟹ 存在连续非一致连续函数          *)
   279|(* ================================================================ *)
   280|
   281|Theorem thm3_not_uc :
   282|  forall E, ~ is_compact E -> has_limit_point_outside E ->
   283|    exists f, continuous_on_E E f /\ ~ uniformly_continuous_on_E E f.
   284|Proof.
   285|  intros E Hnc Hlim_out.
   286|  destruct Hlim_out as [a [Hna Hlim]].
   287|  exists (fun x => / Rabs (x - a)).
   288|  split. apply inv_abs_cont. exact Hna.
   289|  apply inv_abs_not_uc. exact Hna. exact Hlim.
   290|Qed.
   291|
   292|Close Scope R_scope.
   293|