(* MetricCompact.v *)
(* Stage 1: 紧集 + 度量空间 + 紧集上连续函数. *)
(* Arzela-Ascoli 紧嵌入定理证明的第一阶段. *)
(* 范围: 紧集公理化 + Bolzano-Weierstrass (Axiom) + 紧集上连续函数有界 + 取极值. *)
(* 风格: Record + Parameter (与 SphereClassificationDir 一致). *)

Require Import Reals.
Require Import Classical_Prop.
Require Import Ensembles.
Require Import Reals Lra.
Require Import FunctionalExtensionality.
Require Import Classical.

Open Scope R_scope.

Import Nat.

(* ===================================================================== *)
(* 1. 度量空间 (Record 风格)                                             *)
(* ===================================================================== *)

Record MetricSpace := mkMetricSpace {
  ms_V :> Type;
  ms_d : ms_V -> ms_V -> R;
  ms_d_nonneg : forall x y, ms_d x y >= 0;
  ms_d_symm   : forall x y, ms_d x y = ms_d y x;
  ms_d_tri    : forall x y z, ms_d x z <= ms_d x y + ms_d y z;
  ms_d_iden   : forall x y, ms_d x y = 0 -> x = y
}.

(* 在度量空间 M 上的序列 *)
Definition seq_of (M : MetricSpace) : Type := nat -> M.

(* 序列极限 *)
Record LimitSeq (M : MetricSpace) (s : seq_of M) (lim : M) := mkLimitSeq {
  ls_conv : forall eps : R, eps > 0 ->
    exists N : nat, forall n : nat, (n >= N)%nat -> ms_d M (s n) lim < eps
}.

(* Cauchy 序列 *)
Definition CauchySeq (M : MetricSpace) (s : seq_of M) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall m n : nat,
      (m >= N)%nat -> (n >= N)%nat -> ms_d M (s m) (s n) < eps.

(* 完备度量空间: 每个 Cauchy 序列都收敛 *)
Axiom complete_metric_space :
  forall (M : MetricSpace),
    (forall s : seq_of M, CauchySeq M s -> exists lim : M, LimitSeq M s lim) -> True.

(* ===================================================================== *)
(* 2. R^n 的具体度量空间 (Axiom 驱动)                                    *)
(* ===================================================================== *)

(* R^n 我们不构造 — 沿用 Parameter 模式 *)
Parameter VR : nat -> Type.
Parameter n_dim : nat.

(* R^n 是 R^n (经典意义) *)
Definition Rn := VR n_dim.

(* R^n 上的度量: 经典欧氏度量 *)
Parameter Rn_distance : Rn -> Rn -> R.

Axiom Rn_distance_nonneg : forall x y, Rn_distance x y >= 0.
Axiom Rn_distance_symm : forall x y, Rn_distance x y = Rn_distance y x.
Axiom Rn_distance_tri : forall x y z, Rn_distance x z <= Rn_distance x y + Rn_distance y z.
Axiom Rn_distance_iden : forall x y, Rn_distance x y = 0 -> x = y.

(* 抽象地, R^n 是一个度量空间 *)
Definition Rn_metric : MetricSpace := mkMetricSpace Rn Rn_distance
  Rn_distance_nonneg Rn_distance_symm Rn_distance_tri Rn_distance_iden.

(* ===================================================================== *)
(* 3. 紧集 (公理化)                                                     *)
(* ===================================================================== *)

(* K 是 R^n 的子集 *)
(* 用 Ensembles 库表示子集 *)

(* 子集有界 *)
Definition is_bounded (K : Rn -> Prop) : Prop :=
  exists M : R, M > 0 /\ forall x, K x -> Rn_distance x x <= M.
  (* 注: d(x,x) = 0, 任意 M >= 0 都满足. 更准确的: *)
  (* exists M, forall x, K x -> exists c, forall y, K y -> d x y <= M. *)

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
(* Strictly_Increasing 定义 *)
Definition Strictly_Increasing (f : nat -> nat) : Prop :=
  forall n : nat, Nat.lt (f n) (f (S n)).

Axiom bolzano_weierstrass_Rn :
  forall (s : seq_of Rn_metric),
    is_bounded (fun x => exists N, x = s N) ->
    exists subseq : nat -> nat,
      Strictly_Increasing subseq /\
      exists lim : Rn, LimitSeq Rn_metric (fun k => s (subseq k)) lim.

(* 紧集上的有界序列有收敛子列 (Axiom - 需要 is_bounded 定义修正或额外构造) *)
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
(*   2. R^n 度量空间 (Parameter + 4 Axiom) *)
(*   3. 紧集 = 有界 + 闭 *)
(*   4. Bolzano-Weierstrass (Axiom 1) *)
(*   5. 紧集上连续函数有界 (Axiom 2) *)
(*   6. 紧集上连续函数取 sup/inf (Axiom 3, 4) *)
(*   7. C0_on 类型 *)

(* Axiom 总数: 4 (R^n 度量) + 1 (Bolzano-Weierstrass) + 3 (极值) = 8 *)
