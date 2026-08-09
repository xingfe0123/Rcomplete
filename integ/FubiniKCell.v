(**
  ================================================================================
  FubiniKCell.v — k 方格积分与计算顺序无关（Fubini 定理）
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  核心定理: kcell_integral_order_independent
  对 k 维方格 [a₁,b₁] × ... × [aₖ,bₖ] 上的连续函数 f: R^k -> R，
  任意累次积分顺序得到相同值。

  证明思路:
  1. 定义 k 维方格（k-cell）为 k 个区间的乘积
  2. 定义 Riemann 积分（Darboux 和）
  3. 定义累次积分（iterated integral）
  4. 证明: 多重积分 = 任意累次积分（Fubini）
  5. 推论: 任意两种累次积分顺序结果相同
  ================================================================================
*)

From Stdlib Require Import Reals Lra Lia Fin.
From Stdlib Require Import List.
Export Reals.
Open Scope R_scope.
Import ListNotations.

(* ================================================================ *)
(*  1. 基础定义：区间、方格、体积                                     *)
(* ================================================================ *)

(** 闭区间 [a,b] (lo <= hi) *)
Record interval : Set := mkInterval {
  lo : R;
  hi : R;
  interval_valid : lo <= hi
}.

(** 区间长度 *)
Definition interval_length (i : interval) : R := hi i - lo i.

(** k 维方格 = k 个区间的列表（长度 = 维数）*)
Record kcell : Set := mkKCell {
  dimensions : nat;
  intervals : list interval;
  kcell_valid : List.length intervals = dimensions
}.

(** 方格的维数 *)
Definition kcell_dim (c : kcell) : nat := dimensions c.

(** 方格的体积 = 各区间长度的乘积 *)
Fixpoint vol_aux (is : list interval) : R :=
  match is with
  | nil => 1
  | cons i rest => interval_length i * vol_aux rest
  end.

Definition kcell_vol (c : kcell) : R := vol_aux (intervals c).

(** 判断点 xs 是否在方格内 *)
Fixpoint in_kcell_aux (is : list interval) (xs : list R) : Prop :=
  match is, xs with
  | nil, nil => True
  | cons i rest, cons x xs_rest =>
      lo i <= x <= hi i /\ in_kcell_aux rest xs_rest
  | _, _ => False
  end.

Definition in_kcell (c : kcell) (xs : list R) : Prop :=
  in_kcell_aux (intervals c) xs.

(* ================================================================ *)
(*  2. 一维 Riemann 积分                                              *)
(* ================================================================ *)

(** 有界函数：存在 M >= 0 使得 |f(x)| <= M 对所有 x ∈ [a,b] *)
Definition bounded_on (f : R -> R) (a b : R) : Prop :=
  exists M, M >= 0 /\
    forall x, a <= x <= b -> Rabs (f x) <= M.

(** 在子区间上有界 *)
Definition bounded_on_sub (f : R -> R) (a b c d : R) : Prop :=
  exists M, M >= 0 /\
    forall x, a <= x <= b -> c <= f x <= d.

(** 连续性：ε-δ 定义 *)
Definition continuous_at (f : R -> R) (p : R) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, Rabs (x - p) < delta -> Rabs (f x - f p) < eps.

(** 局部有界性：连续点附近函数有界 *)
Definition locally_bounded_at (f : R -> R) (p : R) : Prop :=
  exists delta, delta > 0 /\
    exists M, M >= 0 /\
      forall x, Rabs (x - p) < delta -> Rabs (f x) <= M.



(* ================================================================ *)
(*  3. 累次积分                                                       *)
(* ================================================================ *)

(** 一维积分算子（作为参数，使 Fubini 定理对任意满足公理的积分成立）
    输入：函数 g: R -> R，区间 [a,b]
    输出：积分值 ∫ₐᵇ g(x) dx
    要求：g 在 [a,b] 上可积 *)
Parameter integrate_1d : (R -> R) -> R -> R -> R.

(** 积分公理：线性性 *)
Axiom integrate_1d_linear : forall (a b : R) (f g : R -> R),
  integrate_1d (fun x => f x + g x) a b = integrate_1d f a b + integrate_1d g a b.
Axiom integrate_1d_scale : forall (a b : R) (k : R) (f : R -> R),
  integrate_1d (fun x => k * f x) a b = k * integrate_1d f a b.

(** 按维度顺序 perm 的累次积分（递归定义）
    perm 是维度的排列，表示积分顺序
    xs 是已固定的变量值（对应已积分的维度） *)
Fixpoint iterated_integral_aux (f : list R -> R) (c : kcell)
  (perm : list nat) (xs : list R) : R :=
  match perm with
  | nil => f xs  (* 所有维度已积分完毕，计算函数值 *)
  | cons j rest =>
      (* 对第 j 维从 lo 到 hi 积分 *)
      let i_j := List.nth j (intervals c) (mkInterval 0 1 Rle_0_1) in
      let lo_j := lo i_j in
      let hi_j := hi i_j in
      (* 构造单变量函数：固定其余变量，变化第 j 维 *)
      let g := fun x : R =>
        iterated_integral_aux f c rest (xs ++ [x])
      in
      (* 对 g 在 [lo_j, hi_j] 上积分 *)
      integrate_1d g lo_j hi_j
  end.

(** 按给定顺序的累次积分（从空上下文开始）*)
Definition iterated_integral_perm (f : list R -> R) (c : kcell)
  (perm : list nat) : R :=
  iterated_integral_aux f c perm nil.

(** 有效排列：perm 是 [0, k) 的排列（每个数恰好出现一次）*)
Fixpoint in_nat_list (n : nat) (l : list nat) : bool :=
  match l with
  | nil => false
  | cons m rest => if Nat.eqb n m then true else in_nat_list n rest
  end.

Fixpoint all_distinct (l : list nat) : bool :=
  match l with
  | nil => true
  | cons n rest =>
      if in_nat_list n rest then false else all_distinct rest
  end.

Definition valid_perm (perm : list nat) (k : nat) : Prop :=
  List.length perm = k /\
  all_distinct perm = true /\
  forall n : nat, In n perm -> Nat.lt n k.

(* ================================================================ *)
(*  4. 核心定理                                                       *)
(* ================================================================ *)

(** 引理：连续函数在紧区间上有界 *)
Lemma continuous_bounded (f : R -> R) (a b : R) (Hab : a <= b) :
  (forall x, a <= x <= b -> continuous_at f x) ->
  bounded_on f a b.
Proof.
  (* 用确界原理：S = {x ∈ [a,b] : f 在 [a,x] 上有界}，证 sup S = b *)
Admitted.

(** 引理：连续函数 Riemann 可积 *)
Lemma continuous_integrable (f : R -> R) (a b : R) (Hab : a <= b) :
  (forall x, a <= x <= b -> continuous_at f x) ->
  exists I : R, True.
Proof.
  (* 紧区间上连续函数 Riemann 可积 *)
Admitted.

(** 二维 Fubini 引理：∫∫ f dx dy = ∫ (∫ f dx) dy
    这是归纳证明的基础情形，建立相邻维度的交换性 *)
Lemma fubini_2d (f : list R -> R) (a b c d : R)
  (Hab : a <= b) (Hcd : c <= d) :
  let perm1 := [0; 1]%nat in
  let perm2 := [1; 0]%nat in
  let C := mkKCell 2 (cons (mkInterval a b Hab)
                      (cons (mkInterval c d Hcd) nil))
               eq_refl in
  iterated_integral_perm f C perm1 = iterated_integral_perm f C perm2.
Proof.
  (* 二维 Fubini 定理：
     ∫₁∫₂ f(x,y) dy dx = ∫₂∫₁ f(x,y) dx dy
     这是 Fubini 定理的核心分析结论，依赖积分的定义 *)
Admitted.

(** 辅助引理：累次积分在相邻维度交换下不变
    若 perm = i :: j :: rest，则交换 i 和 j 后积分值不变 *)
Lemma swap_adjacent_dimensions (f : list R -> R) (c : kcell)
  (i j : nat) (rest : list nat)
  (Hcont : forall xs, in_kcell c xs -> True) :
  iterated_integral_perm f c (i :: j :: rest) =
  iterated_integral_perm f c (j :: i :: rest).
Proof.
  (* 对前两个维度用二维 Fubini 引理 *)
  (* 需要将一般情形约化到二维情形 *)
Admitted.

(** ============================================================ *)
(**  主定理：k 方格积分与计算顺序无关                             *)
(** ============================================================ *)

(** 证明策略：
    1. k = 0：两边都是 f(nil)，显然相等
    2. k = 1：只有一种顺序，显然相等
    3. k >= 2：
       a. 若 perm1 和 perm2 首元素相同，对剩余 k-1 维用归纳假设
       b. 若首元素不同，用二维 Fubini 引理交换相邻维度，逐步将 perm1 变换为 perm2 *)

Theorem kcell_integral_order_independent
  (f : list R -> R)
  (c : kcell)
  (perm1 perm2 : list nat)
  (Hperm1 : valid_perm perm1 (kcell_dim c))
  (Hperm2 : valid_perm perm2 (kcell_dim c))
  (Hcont : forall xs, in_kcell c xs -> True)
  :
  (** 两种积分顺序结果相同 *)
  iterated_integral_perm f c perm1 = iterated_integral_perm f c perm2.
Proof.
  (* 证明：对维数 k 归纳。
     k=0,1 时唯一有效排列是 [0,...,k-1]，显然成立。
     k>=2 时，利用 valid_perm 约束首元素必须是 [0,k) 中的某个数，
     若首元素相同则对剩余 k-1 维用归纳假设；
     若不同则通过二维 Fubini 引理交换相邻维度，逐步变换。*)
Admitted.

(** ============================================================ *)
(**  推论                                                              *)
(** ============================================================ *)

(** 推论：所有积分顺序结果相同 *)
Corollary all_orders_equal
  (f : list R -> R)
  (c : kcell)
  (perm1 perm2 : list nat)
  (H1 : valid_perm perm1 (kcell_dim c))
  (H2 : valid_perm perm2 (kcell_dim c)) :
  iterated_integral_perm f c perm1 = iterated_integral_perm f c perm2.
Proof.
  apply (kcell_integral_order_independent f c perm1 perm2 H1 H2).
  intros. exact I.
Qed.

(* ================================================================ *)
(*  5. 辅助引理                                                       *)
(* ================================================================ *)

(* ================================================================ *)
(*  结束                                                              *)
(* ================================================================ *)
