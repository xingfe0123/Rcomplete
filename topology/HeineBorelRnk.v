
(*
  HeineBorelRnk.v — R^n 中紧集、无限子集与极限点
  定理：若 E 是紧集 K 的无限子集，则 E 在 K 中有极限点。

  自包含模块：仅依赖 Rocq Stdlib (Reals, ClassicalEpsilon, List, Fin)。
  不依赖 RicciFlow 项目结构。
*)

From Stdlib Require Import Reals.
From Stdlib Require Import List.
From Stdlib Require Import Fin.
From Stdlib Require Import ClassicalEpsilon.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Utf8.
From Stdlib Require Import Arith.
From Stdlib Require Import FinSets.
From Stdlib Require Import ConstructiveEpsilon.

Import ListNotations.
Open Scope R_scope.

(* ================================================================ *)
(*  1. 欧氏空间 R^n                                                *)
(* ================================================================ *)

(* R^n ≅ Fin.t n → R *)
Definition Rn (n : nat) := Fin.t n -> R.

(* 向量减法 *)
Definition vsub {n : nat} (u v : Rn n) : Rn n := fun i => (u i - v i)%R.

(* 欧氏范数平方 *)
Definition euclidean_sqnorm {n : nat} (v : Rn n) : R :=
  fin_sum n (fun i : Fin.t n => (v i)^2)%R.

(* 欧氏范数 *)
Definition euclidean_norm {n : nat} (v : Rn n) : R :=
  sqrt (euclidean_sqnorm v).

(* 开球 B(c, r) *)
Definition open_ball {n : nat} (c : Rn n) (r : R) (x : Rn n) : Prop :=
  euclidean_norm (vsub x c) < r.

(* 开球范数引理：B(c,r)(x) ⇔ |x-c| < r *)
Lemma open_ball_norm : forall n (c : Rn n) (r : R) (x : Rn n),
  open_ball c r x <-> euclidean_norm (vsub x c) < r.
Proof. intros. unfold open_ball. tauto. Qed.

(* R^n 中的开集：每个点有开球邻域含于 U *)
Definition open_in_Rn (n : nat) (U : Rn n -> Prop) : Prop :=
  forall x : Rn n, U x ->
    exists r : R, r > 0 /\ forall y : Rn n, open_ball x r y -> U y.

(* fin_sum 定义 *)
Definition fin_sum (n : nat) : (Fin.t n -> R) -> R :=
  nat_rect (fun m : nat => (Fin.t m -> R) -> R)
    (fun _ : Fin.t 0 -> R => 0%R)
    (fun (m : nat) (ih : (Fin.t m -> R) -> R) (f : Fin.t (S m) -> R) =>
      (f Fin.F1 + ih (fun i : Fin.t m => f (Fin.FS i)))%R)
    n.

(* R^n 的开集判定用开球 *)
Lemma open_in_Rn_via_balls : forall n (U : Rn n -> Prop),
  open_in_Rn n U <->
  (forall x, U x -> exists r, r > 0 /\ forall y, open_ball x r y -> U y).
Proof. intros. unfold open_in_Rn. tauto. Qed.

(* ================================================================ *)
(*  2. 子空间拓扑：K ⊆ R^n 上的开集                                *)
(* ================================================================ *)

(* U 在 K 中开 ⇔ U = V ∩ K，其中 V 在 R^n 中开 *)
Definition open_in_K {n : nat} (K : Rn n -> Prop) (U : Rn n -> Prop) : Prop :=
  exists V : Rn n -> Prop, open_in_Rn n V /\ forall x, U x <-> V x /\ K x.

(* K 的开覆盖：一族 K-开集的集合覆盖 K *)
Definition cover_K {n : nat} (K : Rn n -> Prop) (F : (Rn n -> Prop) -> Prop) : Prop :=
  (forall U, F U -> open_in_K K U) /\
  (forall x, K x -> exists U, F U /\ U x).

(* ================================================================ *)
(*  3. 紧性定义                                                    *)
(* ================================================================ *)

(* K 是紧的：每个 K-开覆盖有有限子覆盖 *)
Definition compact_in_K {n : nat} (K : Rn n -> Prop) : Prop :=
  forall (F : (Rn n -> Prop) -> Prop),
    cover_K K F ->
    exists (subcover : list (Rn n -> Prop)),
      (forall U, In U subcover -> F U) /\
      (forall x, K x -> exists U, In U subcover /\ U x).

(* ================================================================ *)
(*  4. 无限集                                                      *)
(* ================================================================ *)

(* E 无限 ⇔ 存在 nat → E 的单射 *)
Definition infinite {n : nat} (E : Rn n -> Prop) : Prop :=
  exists (f : nat -> Rn n),
    (forall i, E (f i)) /\ (forall i j, f i = f j -> i = j).

(* ================================================================ *)
(*  5. 极限点                                                      *)
(* ================================================================ *)

(* p 是 E 在 K 中的极限点：
   ∀ε>0, (B(p,ε) ∩ E) \ {p} 非空，且 p ∈ K *)
Definition limit_point_in_K {n : nat} (K : Rn n -> Prop) (E : Rn n -> Prop) (p : Rn n) : Prop :=
  K p /\
  forall r : R, r > 0 ->
    exists x, E x /\ p <> x /\ open_ball p r x.

(* ================================================================ *)
(*  6. 基本引理                                                    *)
(* ================================================================ *)

(* 有限集 *)
Definition finite {n : nat} (E : Rn n -> Prop) : Prop :=
  exists (N : nat), exists (f : {k : nat | k < N} -> Rn n),
    (forall x, E x -> exists i, f i = x) /\
    (forall i j, f i = f j -> i = j).

(* 无限集不是有限的 *)
Lemma infinite_not_finite : forall n (E : Rn n -> Prop),
  infinite E -> ~ finite E.
Proof.
  intros n E Hinf Hfin.
  destruct Hinf as [f [Hf1 Hf2]].
  destruct Hfin as [N [g [Hg1 Hg2]]].
  (* 用鸽巢原理：N+1 个不同元素映射到 N 个槽，矛盾 *)
  (* 构造序列 e_i = f(i)，i=0..N *)
  (* 每个 e_i ∈ E，由 Hg1 存在 j < N 使 g(j) = e_i *)
  (* 但 f 是单射，e_0,...,e_N 共 N+1 个不同元素 *)
  (* 由鸽巢原理，存在 i1 < i2 ≤ N 使 g(j1) = g(j2) 且 j1≠j2 或 f(i1)=f(i2) *)
  (* 具体地，考虑函数 h : {i | i ≤ N} → {j | j < N}, h(i) = Hg1(e_i) *)
  (* 由 PeanoNat 的鸽巢原理，存在 i1 < i2 使 h(i1) = h(i2) *)
  (* 即 g(j) = e_{i1} 且 g(j) = e_{i2}，故 e_{i1} = e_{i2} *)
  (* 但 f 是单射，故 i1 = i2，矛盾 *)
Admitted.

(* 从无限集中递归提取不同元素序列 *)
Lemma infinite_seq_lemma : forall n (E : Rn n -> Prop),
  infinite E ->
  exists (f : nat -> Rn n), (forall i, E (f i)) /\ (forall i j, f i = f j -> i = j).
Proof.
  intros n E Hinf.
  destruct Hinf as [f [Hf1 Hf2]].
  exists f. tauto.
Qed.

(* ================================================================ *)
(*  7. 核心定理                                                    *)
(* ================================================================ *)

(* 引理：若 p ∈ K 不是 E 的极限点，则存在邻域至多含 E 中一个点 *)
Lemma not_limit_point_has_small_ball : forall n (K : Rn n -> Prop) (E : Rn n -> Prop) (p : Rn n),
  K p -> ~ limit_point_in_K K E p ->
  exists r : R, r > 0 /\ forall x, open_ball p r x -> E x -> x = p.
Proof.
  intros n K E p Hkp Hnlim.
  unfold limit_point_in_K in Hnlim.
  apply not_all_ex_not in Hnlim.
  destruct Hnlim as [r Hr].
  exists r.
  split.
  - apply Hr.
  - intros x Hball HE.
    (* 反证：若 x ≠ p，则 x 是极限点 *)
    assert (Hcontra : exists x, E x /\ p <> x /\ open_ball p r x).
    { exists x. tauto. }
    exfalso.
    (* 这与 ~limit_point_in_K 矛盾 *)
    unfold limit_point_in_K.
    assert (Hlim : K p /\ (forall r : R, r > 0 -> exists x, E x /\ p <> x /\ open_ball p r x)).
    { split; [exact Hkp | intros r' Hr'. destruct (Rle_lt_dec r' r). }
Admitted.

(* 引理：紧集的无限子集必有极限点 *)
Theorem infinite_subset_has_limit_point_in_compact : forall n (K : Rn n -> Prop) (E : Rn n -> Prop),
  compact_in_K K ->
  (forall x, E x -> K x) ->
  infinite E ->
  exists p, limit_point_in_K K E p.
Proof.
  (* 证明思路：
     1. 假设 E 在 K 中没有极限点
     2. 对每个 p ∈ K，找到邻域至多含 E 中一个点
     3. 这些邻域构成 K 的开覆盖
     4. 由紧性，存在有限子覆盖
     5. 有限个邻域，每个至多含 E 中一个点 ⇒ E 有限
     6. 与 E 无限矛盾 *)
Admitted.

(* ================================================================ *)
(*  8. 等价定义：K 在 R^n 中紧 ⇔ K 闭且有界 (Heine-Borel)          *)
(* ================================================================ *)

(* 有界 *)
Definition bounded {n : nat} (K : Rn n -> Prop) : Prop :=
  exists c R, R > 0 /\ forall x, K x -> euclidean_norm (vsub x c) <= R.

(* 闭 *)
Definition closed_in_Rn {n : nat} (K : Rn n -> Prop) : Prop :=
  forall x, (forall r, r > 0 -> exists y, K y /\ open_ball x r y) -> K x.

(* Heine-Borel 定理 *)
Theorem Heine_Borel_Rn : forall n (K : Rn n -> Prop),
  compact_in_K K <-> closed_in_Rn K /\ bounded K.
Proof.
  (* 这是 R^n 上的完整 Heine-Borel 定理 *)
Admitted.

(* ================================================================ *)
(*  9. 完整等价链                                                  *)
(* ================================================================ *)

(* 主定理：以下三者等价：
   (1) K 紧
   (2) K 闭且有界
   (3) K 的每个无限子集在 K 中有极限点 *)

Theorem compact_iff_limit_point_property : forall n (K : Rn n -> Prop),
  compact_in_K K <->
  (forall E : Rn n -> Prop, (forall x, E x -> K x) -> infinite E ->
    exists p, limit_point_in_K K E p).
Proof.
  intros n K.
  split.
  - (* 紧 ⇒ 极限点性质 *)
    intros Hcompact E HEinf.
    apply infinite_subset_has_limit_point_in_compact.
    + exact Hcompact.
    + exact HEinf.
  - (* 极限点性质 ⇒ 紧 *)
    (* 若 K 不紧，则存在开覆盖无有限子覆盖
       由此构造无限子集无极限点 *)
Admitted.

(* 终极定理：紧 ⇔ 闭且有界 ⇔ 极限点性质 *)
Theorem main_equivalence : forall n (K : Rn n -> Prop),
  compact_in_K K <-> (closed_in_Rn K /\ bounded K) /\
  (forall E, (forall x, E x -> K x) -> infinite E ->
    exists p, limit_point_in_K K E p).
Proof.
  intros n K.
  split.
  - intros Hcompact.
    split.
    + split.
      * apply Heine_Borel_Rn in Hcompact. tauto.
      * apply compact_iff_limit_point_property. exact Hcompact.
  - intros [[Hclosed Hbounded] Hlimit].
    apply compact_iff_limit_point_property. exact Hlimit.
Qed.
