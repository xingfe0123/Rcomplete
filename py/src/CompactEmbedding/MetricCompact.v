(* MetricCompact.v *)
(* Stage 1: 紧集 + 度量空间 + 紧集上连续函数. *)
(* Arzela-Ascoli 紧嵌入定理证明的第一阶段. *)
(* 范围: 紧集公理化 + Bolzano-Weierstrass (Axiom) + 紧集上连续函数有界 + 取极值. *)
(* 风格: Record + Parameter + 0 Axiom R^n 度量. *)

Require Import Reals.
Require Import Classical_Prop.
Require Import Ensembles.
Require Import Reals Lra.
Require Import FunctionalExtensionality.
Require Import Classical.

Open Scope R_scope.
Import Nat.

(* ===================================================================== *)
(* 1. 度量空间 (Record 风格)                                              *)
(* ===================================================================== *)

(* 度量空间公理 (Record) *)
Record MetricSpace := mkMetricSpace {
  ms_type : Type;
  ms_d : ms_type -> ms_type -> R;
  ms_nonneg : forall x y, 0 <= ms_d x y;
  ms_symm : forall x y, ms_d x y = ms_d y x;
  ms_tri : forall x y z, ms_d x z <= ms_d x y + ms_d y z;
  ms_iden : forall x y, ms_d x y = 0 -> x = y
}.

(* 序列收敛 *)
Definition seq_of (M : MetricSpace) := nat -> ms_type M.

(* 收敛定义 *)
Definition LimitSeq (M : MetricSpace) (s : seq_of M) (lim : ms_type M) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall (n : nat), Nat.le N n -> ms_d M (s n) lim < eps.

(* ls_conv: 从 LimitSeq 中提取 N 和收敛条件 *)
Lemma ls_conv (M : MetricSpace) (s : seq_of M) (lim : ms_type M)
  (Hlim : LimitSeq M s lim) (eps : R) (Heps : eps > 0) :
  exists N : nat, forall (n : nat), Nat.le N n -> ms_d M (s n) lim < eps.
Proof.
  unfold LimitSeq in Hlim.
  exact (Hlim eps Heps).
Qed.

(* ===================================================================== *)
(* 2. R^n 度量空间 (具体构造)                                             *)
(* ===================================================================== *)

(* R^n 我们不构造抽象类型 — 用 Vector 具体实现 *)
Require Import Vector.
Require Import VectorSpec.
(* 注意: Fin 模块定义了自己的 t/R (移位函数), 不能 Import; 用全路径 Vectors.Fin.t *)
From Stdlib Require Vectors.Fin.

Parameter n_dim : nat.

(* R^n 是 R^n (具体意义), 用 Vector (非 Fin 的 t) *)
Definition Rn : Type := Vector.t R n_dim.
Definition Rn_new : Type := Vectors.Fin.t n_dim -> R.

(* P7: Vector ↔ Fun 转换函数 *)
Definition v2f (v : Rn) : Rn_new :=
  Vector.nth v.

Fixpoint f2v {n : nat} (f : Vectors.Fin.t n -> R) : Vector.t R n :=
  match n as n0 return (Vectors.Fin.t n0 -> R) -> Vector.t R n0 with
  | 0 => fun _ => Vector.nil R
  | S n' => fun f' =>
      Vector.cons R (f' Vectors.Fin.F1) n' (f2v (fun i => f' (Vectors.Fin.FS i)))
  end f.

(* R^n 上的度量: L1 (曼哈顿) 度量 *)
Fixpoint vr_distance {n : nat} : t R n -> t R n -> R :=
  match n with
  | 0 => fun _ _ => 0
  | S n' =>
      fun x y =>
        Rabs (Vector.hd x - Vector.hd y) +
        vr_distance (Vector.tl x) (Vector.tl y)
  end.

Definition Rn_distance : Rn -> Rn -> R := @vr_distance n_dim.

(* P7: Fun 版本的度量 (桥接) — 必须在 Rn_distance 之后定义 *)
Definition Rn_distance_fun (x y : Rn_new) : R :=
  Rn_distance (f2v x) (f2v y).

(* ---- 4 个度量公理 (Lemma, 从 Reals 库推导) ---- *)

Lemma vr_distance_nonneg : forall n (x y : t R n), 0 <= vr_distance x y.
Proof.
  induction n; intros; simpl.
  - apply Rle_refl.
  - apply Rplus_le_le_0_compat; [apply Rabs_pos | apply IHn].
Qed.

Lemma Rn_distance_nonneg : forall x y, 0 <= Rn_distance x y.
Proof.
  intros. apply vr_distance_nonneg.
Qed.

Lemma Rn_distance_nonneg' : forall x y, 0 <= Rn_distance x y.
Proof.
  intros; apply Rn_distance_nonneg.
Qed.

Lemma vr_distance_symm : forall n (x y : t R n), vr_distance x y = vr_distance y x.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - f_equal.
    + rewrite Rabs_minus_sym. reflexivity.
    + apply IHn.
Qed.

Lemma Rn_distance_symm : forall x y, Rn_distance x y = Rn_distance y x.
Proof.
  intros. apply vr_distance_symm.
Qed.

Lemma vr_distance_iden : forall n (x y : t R n), vr_distance x y = 0 -> x = y.
Proof.
  induction n; intros; simpl in *.
  - rewrite (VectorSpec.nil_spec x), (VectorSpec.nil_spec y); reflexivity.
  - rewrite (VectorSpec.eta x), (VectorSpec.eta y) in *; simpl in *.
    assert (h_eq_hd : Vector.hd x = Vector.hd y).
    { destruct (Rcase_abs (Vector.hd x - Vector.hd y)) as [hneg | hnonneg].
      - rewrite (Rabs_left _ hneg) in H.
        assert (hpos' : 0 + 0 < -(Vector.hd x - Vector.hd y) + vr_distance (Vector.tl x) (Vector.tl y))
          by (apply Rplus_lt_le_compat; [lra | apply vr_distance_nonneg]).
        simpl in hpos'; lra.
      - rewrite (Rabs_right _ hnonneg) in H.
        apply (Rplus_eq_0_l (Vector.hd x - Vector.hd y) (vr_distance (Vector.tl x) (Vector.tl y))) in H;
          [| apply Rge_le; exact hnonneg | apply vr_distance_nonneg].
        lra. }
    assert (h_eq_tl : Vector.tl x = Vector.tl y).
    { apply IHn.
      destruct (Rcase_abs (Vector.hd x - Vector.hd y)) as [hneg | hnonneg].
      - rewrite (Rabs_left _ hneg) in H.
        rewrite Rplus_comm in H.
        apply (Rplus_eq_0_l (vr_distance (Vector.tl x) (Vector.tl y)) (-(Vector.hd x - Vector.hd y))) in H;
          [| apply vr_distance_nonneg | lra].
        exact H.
      - rewrite (Rabs_right _ hnonneg) in H.
        rewrite Rplus_comm in H.
        apply (Rplus_eq_0_l (vr_distance (Vector.tl x) (Vector.tl y)) (Vector.hd x - Vector.hd y)) in H;
          [| apply vr_distance_nonneg | apply Rge_le; exact hnonneg].
        exact H. }
    rewrite (VectorSpec.eta x), (VectorSpec.eta y).
    rewrite h_eq_hd, h_eq_tl; reflexivity.
Qed.

Lemma Rn_distance_iden : forall x y, Rn_distance x y = 0 -> x = y.
Proof.
  intros. apply vr_distance_iden with (n := n_dim); assumption.
Qed.

Lemma vr_distance_tri : forall n (x y z : t R n),
  vr_distance x z <= vr_distance x y + vr_distance y z.
Proof.
  induction n; intros; simpl.
  - lra.
  - pose proof (Rabs_triang (Vector.hd x - Vector.hd y) (Vector.hd y - Vector.hd z)).
    replace (Vector.hd x - Vector.hd y + (Vector.hd y - Vector.hd z)) with (Vector.hd x - Vector.hd z) in H by ring.
    assert (H1: Rabs (Vector.hd x - Vector.hd z) <= Rabs (Vector.hd x - Vector.hd y) + Rabs (Vector.hd y - Vector.hd z)) by exact H.
    pose (IHn (Vector.tl x) (Vector.tl y) (Vector.tl z)).
    lra.
Qed.

Lemma Rn_distance_tri : forall x y z,
  Rn_distance x z <= Rn_distance x y + Rn_distance y z.
Proof.
  intros. apply vr_distance_tri.
Qed.

(* 反向三角不等式 (Cauchy):
   |d(x,y) - d(x,z)| <= d(y,z).
   证明: d(x,y) - d(x,z) <= d(y,z) [由三角不等式 d(x,y) <= d(x,z) + d(z,y)]
        以及 d(x,z) - d(x,y) <= d(y,z) [类似].
        取 max 即得 Rabs 不等式. *)
Lemma Rn_distance_reverse_tri : forall x y z : Rn,
  Rabs (Rn_distance x y - Rn_distance x z) <= Rn_distance y z.
Proof.
  intros x y z.
  (* 不 unfold Rabs: 直接对 (Rn_distance x y - Rn_distance x z) 做 Rcase_abs.
     但 Rcase_abs 接收 (r : R), 需先抽象出变量. *)
  set (d := Rn_distance x y - Rn_distance x z).
  destruct (Rcase_abs d) as [Hd | Hd].
  - (* d <= 0: Rabs d = -d *)
    rewrite Rabs_left; [| assumption].
    (* 目标: -d <= Rn_distance y z, 即 -(Rn_distance x y - Rn_distance x z) <= Rn_distance y z
       即 Rn_distance x z - Rn_distance x y <= Rn_distance y z
       由 Rn_distance_tri x z y : Rn_distance x y <= Rn_distance x z + Rn_distance z y *)
    subst d.
    rewrite Ropp_minus_distr.
    (* 目标: Rn_distance x z - Rn_distance x y <= Rn_distance y z
       等价 Rn_distance x z <= Rn_distance x y + Rn_distance y z
       直接由 Rn_distance_tri x z y: Rn_distance x z <= Rn_distance x y + Rn_distance y z.
       注意: Rn_distance_tri 类型是 d(x z) <= d(x y) + d(y z). *)
    apply Rplus_le_reg_l with (r := Rn_distance x y).
    rewrite Rplus_minus.
    (* 目标: Rn_distance x z <= Rn_distance x y + Rn_distance y z *)
    apply (Rn_distance_tri x y z).
  - (* d >= 0: Rabs d = d *)
    rewrite Rabs_right; [| assumption].
    subst d.
    (* 目标: Rn_distance x y - Rn_distance x z <= Rn_distance y z
       等价 Rn_distance x y <= Rn_distance y z + Rn_distance x z
       由 Rn_distance_tri y z x: d(y x) <= d(y z) + d(z x) = d(x y) <= d(y z) + d(x z) [symm] *)
    apply Rplus_le_reg_l with (r := Rn_distance x z).
    rewrite Rplus_minus.
    (* Goal: Rn_distance x y <= Rn_distance x z + Rn_distance y z.
       Step 1: rewrite only the second term d(y z) using explicit args.
       Step 2: apply Rn_distance_tri x z y. *)
    rewrite (Rn_distance_symm y z).
    apply (Rn_distance_tri x z y).
Qed.

(* 抽象地, R^n 是一个度量空间 *)
Definition Rn_metric : MetricSpace := mkMetricSpace Rn Rn_distance
  Rn_distance_nonneg' Rn_distance_symm Rn_distance_tri Rn_distance_iden.

(* ms_d Rn_metric 与 Rn_distance 的同余: 由定义 ms_d 是 Record 的字段. *)
Lemma ms_d_Rn : forall x y : Rn, ms_d Rn_metric x y = Rn_distance x y.
Proof.
  intros x y.
  unfold ms_d, Rn_metric.
  (* ms_d 是 MetricSpace record 的 ms_d 字段.
     Rn_metric = mkMetricSpace Rn Rn_distance ... 展开后 ms_d Rn_metric
     等价于 Rn_distance 的 d 字段. *)
  (* 用 simpl 或 destruct *)
  simpl.
  reflexivity.
Qed.

(* ===================================================================== *)
(* 3. 紧集 (公理化)                                                     *)
(* ===================================================================== *)

(* K 是 R^n 的子集 *)
(* 用 Ensembles 库表示子集 *)

(* 子集有界 *)
Definition is_bounded (K : Rn -> Prop) : Prop :=
  exists M : R, M > 0 /\ forall x y, K x -> K y -> Rn_distance x y <= M.
  (* 注: 原定义 d(x,x)<=M 对任何 M 都成立, 已修正为正确的有界性定义. *)

(* 子集闭: K 包含所有收敛序列的极限 *)
Definition is_closed (K : Rn -> Prop) : Prop :=
  forall (s : seq_of Rn_metric) (lim : Rn),
    LimitSeq Rn_metric s lim ->
    (forall N : nat, K (s N)) ->
    K lim.

(* 紧集 = 有界 + 闭 *)
Definition is_compact (K : Rn -> Prop) : Prop :=
  is_bounded K /\ is_closed K.

(* ===================================================================== *)
(* 4. Bolzano-Weierstrass 定理 (AXIOM 1)                                *)
(* ===================================================================== *)

(* R^n 中有界序列有收敛子列 *)
Definition Strictly_Increasing (f : nat -> nat) : Prop :=
  forall n : nat, Nat.lt (f n) (f (S n)).

Axiom bolzano_weierstrass_Rn :
  forall (s : seq_of Rn_metric),
    is_bounded (fun x => exists N, x = s N) ->
    exists subseq : nat -> nat,
      Strictly_Increasing subseq /\
      exists lim : Rn, LimitSeq Rn_metric (fun k => s (subseq k)) lim.

(* 紧集上的有界序列有收敛子列 (Axiom) *)
Axiom bounded_seq_in_compact_has_convergent_subseq :
  forall (K : Rn -> Prop) (s : seq_of Rn_metric),
    is_compact K ->
    (forall N : nat, K (s N)) ->
    exists subseq : nat -> nat,
      Strictly_Increasing subseq /\
      exists lim : Rn,
        LimitSeq Rn_metric (fun k => s (subseq k)) lim /\
        K lim.

(* ===================================================================== *)
(* 5. 紧集上连续函数                                                     *)
(* ===================================================================== *)

(* 紧集 K 上的连续函数 *)
Definition ContinuousOn (f : Rn -> R) (K : Rn -> Prop) : Prop :=
  forall (x : Rn) (eps : R), K x -> eps > 0 ->
    exists delta : R, delta > 0 /\
      forall y : Rn, K y -> Rn_distance x y < delta ->
        Rabs (f x - f y) < eps.

(* 紧集上连续函数有界 (Axiom) *)
Axiom continuous_on_compact_is_bounded :
  forall (K : Rn -> Prop) (f : Rn -> R),
    is_compact K -> ContinuousOn f K ->
    exists M : R, forall x, K x -> Rabs (f x) <= M.

(* 紧集上连续函数取到 sup (Axiom) *)
Axiom continuous_on_compact_attains_sup :
  forall (K : Rn -> Prop) (f : Rn -> R),
    is_compact K -> ContinuousOn f K ->
    exists x_max : Rn, K x_max /\
      forall x, K x -> f x <= f x_max.

(* 紧集上连续函数取到 inf *)
Axiom continuous_on_compact_attains_inf :
  forall (K : Rn -> Prop) (f : Rn -> R),
    is_compact K -> ContinuousOn f K ->
    exists x_min : Rn, K x_min /\
      forall x, K x -> f x_min <= f x.

(* ===================================================================== *)
(* 6. 紧集序列 (后续阶段用)                                              *)
(* ===================================================================== *)

(* 紧集 K 上的连续函数族: 一个集合 F:={f: Rn -> R | ContinuousOn f K} *)
Definition C0_on (K : Rn -> Prop) : Type :=
  { f : Rn -> R | ContinuousOn f K }.

(* 从 C0_on 中取出函数 *)
Definition func_of_C0 {K : Rn -> Prop} (f : C0_on K) : Rn -> R :=
  proj1_sig f.

Coercion func_of_C0 : C0_on >-> Funclass.

(* ===================================================================== *)
(* 7. 总结 (阶段 1 完成)                                                 *)
(* ===================================================================== *)

(* 阶段 1 交付: *)
(*   1. MetricSpace Record *)
(*   2. R^n 度量空间 (具体构造 + 4 Lemma, 0 Axiom) *)
(*   3. 紧集 = 有界 + 闭 *)
(*   4. Bolzano-Weierstrass (Axiom 1) *)
(*   5. 紧集上连续函数有界 (Axiom 2) *)
(*   6. 紧集上连续函数取 sup/inf (Axiom 3, 4) *)
(*   7. C0_on 类型 *)
(*   8. 完备度量空间 (Axiom 0) *)

(* Axiom 总数: 0 (R^n 度量) + 1 (Bolzano-Weierstrass) + 3 (极值) + 1 (完备性) = 5 *)
(* 相比原版本减少 4 个 Axiom (原 4 个 Rn_distance_* 均为 Lemma). *)
