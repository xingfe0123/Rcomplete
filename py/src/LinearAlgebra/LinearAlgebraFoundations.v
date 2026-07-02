(* LinearAlgebraFoundations.v *)
(* 线性代数基础: 内积、范数、二次型、矩阵-向量乘法 *)
(* 目标: 为 Phase 1 (Axiom 2 → QED) 提供基础设施 *)

Require Import Reals.
Require Import Reals Lra.
Require Import Coq.Reals.RIneq.
Require Import FunctionalExtensionality.
Require Import Classical.
Require Import List.
Require Import Arith.
Require Import Lia.

Open Scope R_scope.

(* ===================================================================== *)
(* 1. 求和工具 (有限和)                                                  *)
(* ===================================================================== *)

(* 求和: sum_{k=0}^{n-1} f k *)
Fixpoint Rsum (n : nat) (f : nat -> R) : R :=
  match n with
  | 0 => 0
  | S n' => f n' + Rsum n' f
  end.

(* 求和的线性性: sum (a*f + g) = a * sum f + sum g *)
Lemma Rsum_linear :
  forall (n : nat) (f g : nat -> R) (a : R),
    Rsum n (fun k => a * f k + g k) = a * Rsum n f + Rsum n g.
Proof.
  intros n f g a. induction n as [|n' IH].
  - simpl. rewrite (Rmult_0_r a). rewrite Rplus_0_r. reflexivity.
  - simpl. rewrite IH. lra.
Qed.

(* 求和等于自身 *)
Lemma Rsum_ext :
  forall (n : nat) (f g : nat -> R),
    (forall k, Nat.lt k n -> f k = g k) ->
    Rsum n f = Rsum n g.
Proof.
  induction n as [|n' IH].
  - simpl. reflexivity.
  - intros f g H. simpl. f_equal.
    + (* n' < S n' = n, via Nat.lt_succ_r proj2 applied to Nat.le_refl. *)
    rewrite (H n' (proj2 (PeanoNat.Nat.lt_succ_r n' n') (Nat.le_refl n'))). reflexivity.
    + apply IH. intros k Hk. apply H. lia.
Qed.

(* 非空求和 vs 0: sum_{k=0}^{n-1} f k = 0 当所有项为 0 *)
(* 但这不直接给出正性; 我们需要另一个引理 *)

(* 求和中的一项: sum_{k} f k = f i + sum_{k≠i} f k *)
Lemma Rsum_split :
  forall (n : nat) (f : nat -> R) (i : nat),
    Nat.lt i n ->
    Rsum n f = f i + Rsum n (fun k => if Nat.ltb k i then f k
                                     else if Nat.eqb k i then 0
                                     else f k).
Proof.
  (* 这是个比较麻烦的引理, 在此暂以 Axiom 形式封装 *)
Admitted. (* 标记为待证 *)

(* ===================================================================== *)
(* 2. 向量定义 (nat -> R)                                                *)
(* ===================================================================== *)

(* 零向量 *)
Definition zero_vec (n : nat) : nat -> R := fun _ => 0.

(* 向量加法 *)
Definition vec_add (n : nat) (u v : nat -> R) : nat -> R :=
  fun i => u i + v i.

(* 向量数乘 *)
Definition vec_scale (n : nat) (c : R) (v : nat -> R) : nat -> R :=
  fun i => c * v i.

(* 向量相等 *)
Definition vec_eq (n : nat) (u v : nat -> R) : Prop :=
  forall i : nat, u i = v i.

(* ===================================================================== *)
(* 3. 内积 ⟨u, v⟩ = Σ_{k<n} u_k v_k                                      *)
(* ===================================================================== *)

Definition inner_product (n : nat) (u v : nat -> R) : R :=
  Rsum n (fun k => u k * v k).

Notation "u · v" := (inner_product _ u v) (at level 50).

(* 注: 上面的 notation 使用 placeholder _, 在 forall 量词内调用时
   Coq 9 解析失败. 实际定义使用显式 inner_product n u v 形式. *)

(* 内积对称性 *)
Lemma inner_symm :
  forall (n : nat) (u v : nat -> R),
    inner_product n u v = inner_product n v u.
Proof.
  intros n u v. unfold inner_product. apply Rsum_ext. intros k Hk.
  rewrite Rmult_comm. reflexivity.
Qed.

(* 内积线性 (在第一分量) *)
Lemma inner_linear_l :
  forall (n : nat) (a : R) (u1 u2 v : nat -> R),
    inner_product n (vec_scale n a (vec_add n u1 u2)) v
    = a * inner_product n u1 v + a * inner_product n u2 v.
Proof.
  (* Requires inner distributivity over addition in second argument:
     sum_k (a*u1_k + u2_k) * v_k = a * sum_k u1_k*v_k + sum_k u2_k*v_k.
     This needs a separate lemma (distributivity of multiplication over
     addition in summation). We admit. *)
Admitted.

(* 内积线性 (在第二分量) *)
Lemma inner_linear_r :
  forall (n : nat) (a : R) (u v1 v2 : nat -> R),
    inner_product n u (vec_scale n a (vec_add n v1 v2))
    = a * inner_product n u v1 + a * inner_product n u v2.
Proof.
  (* Requires inner distributivity over addition in first argument. *)
Admitted.

(* 内积与数乘相容 *)
Lemma inner_scale :
  forall (n : nat) (a : R) (u v : nat -> R),
    inner_product n (vec_scale n a u) v = a * inner_product n u v.
Proof.
  intros n a u v. unfold inner_product, vec_scale.
  induction n as [|n' IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(* 零向量的内积为 0 *)
Lemma inner_zero_l :
  forall (n : nat) (v : nat -> R),
    inner_product n (zero_vec n) v = 0.
Proof.
  intros n v. unfold inner_product, zero_vec.
  induction n as [|n' IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

(* ===================================================================== *)
(* 4. 范数 ||v||² = ⟨v, v⟩ = Σ v_k²                                      *)
(* ===================================================================== *)

(* 平方范数 *)
Definition norm_sq (n : nat) (v : nat -> R) : R :=
  inner_product n v v.

(* 范数非负 *)
Lemma norm_sq_nonneg :
  forall (n : nat) (v : nat -> R),
    norm_sq n v >= 0.
Proof.
  intros n v. unfold norm_sq, inner_product.
  induction n as [|n' IH].
  - simpl. reflexivity.
  - simpl. rewrite <- IH. (* 递归假设: Rsum n' (fun k => v k * v k) >= 0 *)
    (* 现在需要: v n' * v n' + Rsum n' >= 0 *)
    (* 由 R 有序域: x*x >= 0, 所以 v n' * v n' >= 0 *)
    (* 与一个 >= 0 的数相加仍 >= 0 *)
    admit. (* 此处用 admit 标记, 实际证明: nra 或 lra 处理 x² >= 0 *)
Admitted.

(* 关键引理: ||v||² > 0 ⟺ v ≠ 0 *)
(* 这条很关键! 完整证明需要 R 序性质 + 有限和的正性判定 *)
(* 标准论证: 假设 ||v||² > 0 但 v = 0, 矛盾 (因为 0 = Σ 0² = 0) *)
(* 反向: 若 v ≠ 0, 存在 i 使 v_i ≠ 0, 由 v_i² > 0 且其他项 >= 0 推出总和 > 0 *)

Lemma norm_sq_pos_iff_nonzero :
  forall (n : nat) (v : nat -> R),
    (exists i : nat, Nat.lt i n /\ v i <> 0) <-> norm_sq n v > 0.
Proof.
  intros n v. split.
  - (* => 方向: v ≠ 0 ⇒ ||v||² > 0 *)
    intros [i [Hi Hvi]].
    unfold norm_sq, inner_product.
    (* 需要将 Rsum 拆出 v_i² 这一项 *)
    (* 由于 admit Rsum_split, 这里用更简单的方法: 归纳 + 单调性 *)
Admitted. (* 待证 *)

(* 弱化版本: ||v||² = 0 ⇒ v = 0 (在内部点为零) *)
Lemma norm_sq_zero_implies_zero :
  forall (n : nat) (v : nat -> R),
    (forall i, Nat.lt i n -> v i = 0) ->
    norm_sq n v = 0.
Proof.
  intros n v H. unfold norm_sq, inner_product.
  induction n as [|n' IH]; simpl.
  - reflexivity.
  - rewrite (IH (fun i Hi => H i (Nat.lt_trans i n' (S n') Hi (Nat.lt_succ_diag_r n')))),
            (H n' (Nat.lt_succ_diag_r n')). ring.
Qed.

(* ===================================================================== *)
(* 4.9 矩阵类型定义                                                       *)
(* ===================================================================== *)

Definition Matrix (n : nat) := nat -> nat -> R.

(* ===================================================================== *)
(* 5. 矩阵-向量乘法 (Av)_i = Σ_j A_{ij} v_j                              *)
(* ===================================================================== *)

Definition mat_vec_mult (n : nat) (A : Matrix n) (v : nat -> R) : nat -> R :=
  fun i => Rsum n (fun j => A i j * v j).

Notation "A '⟪' v" := (mat_vec_mult _ A v) (at level 50).

(* Av 的第 i 个分量 *)
Lemma mat_vec_mult_spec :
  forall (n : nat) (A : Matrix n) (v : nat -> R) (i : nat),
    Nat.lt i n -> (A ⟪ v) i = Rsum n (fun j => A i j * v j).
Proof.
  intros. reflexivity.
Qed.

(* A(αv) = α(Av) *)
Lemma mat_vec_mult_scale :
  forall (n : nat) (A : Matrix n) (a : R) (v : nat -> R),
    A ⟪ (vec_scale n a v) = vec_scale n a (A ⟪ v).
Proof.
  intros n A a v. unfold mat_vec_mult, vec_scale.
  apply functional_extensionality. intros i.
  induction n as [|n' IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(* A(u+v) = Au + Av *)
Lemma mat_vec_mult_add :
  forall (n : nat) (A : Matrix n) (u v : nat -> R),
    A ⟪ (vec_add n u v) = vec_add n (A ⟪ u) (A ⟪ v).
Proof.
  intros n A u v. unfold mat_vec_mult, vec_add.
  apply functional_extensionality. intros i.
  induction n as [|n' IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(* ===================================================================== *)
(* 6. 二次型 x^T A x = ⟨x, Ax⟩                                            *)
(* ===================================================================== *)

(* 二次型定义: x^T A x = Σ_i x_i (Ax)_i *)
Definition quadratic_form (n : nat) (A : Matrix n) (x : nat -> R) : R :=
  inner_product n x (A ⟪ x).

(* 二次型 = Σ_{i,j} x_i A_{ij} x_j (展开形式) *)
Lemma quadratic_form_expand :
  forall (n : nat) (A : Matrix n) (x : nat -> R),
    quadratic_form n A x = Rsum n (fun i => x i * Rsum n (fun j => A i j * x j)).
Proof.
  intros n A x. unfold quadratic_form, inner_product, mat_vec_mult. reflexivity.
Qed.

(* 二次型与矩阵乘法的结合: x^T A x = x^T (Ax) *)
(* 已经在定义中, 这里证明它确实是双线性形式 *)
Lemma quadratic_form_bilinear_1 :
  forall (n : nat) (A : Matrix n) (a : R) (x1 x2 : nat -> R),
    quadratic_form n A (vec_add n x1 x2) =
    quadratic_form n A x1 + quadratic_form n A x2 +
    a * inner_product n x1 (A ⟪ x2) + a * inner_product n x2 (A ⟪ x1).
Proof.
Admitted.

(* 重要性质: 对称矩阵的二次型满足 x^T A x = x^T A^T x = x^T (A+A^T)/2 x *)
(* 但对于对称 A: A = A^T, 所以 x^T A x = ⟨x, Ax⟩ *)

(* ===================================================================== *)
(* 7. 核心引理: 特征方程 v^T A v = λ ||v||²                              *)
(* ===================================================================== *)

(* 若 Av = λv, 则 ⟨v, Av⟩ = ⟨v, λv⟩ = λ ⟨v,v⟩ *)
Lemma eigenvector_quadratic :
  forall (n : nat) (A : Matrix n) (v : nat -> R) (lambda : R),
    (forall i, Nat.lt i n -> (A ⟪ v) i = lambda * v i) ->
    quadratic_form n A v = lambda * norm_sq n v.
Proof.
  intros n A v lambda H.
  unfold quadratic_form, inner_product, norm_sq, mat_vec_mult.
  (* 等式: Σ_i v_i * (Σ_j A_{ij} v_j) = Σ_i v_i * (lambda * v_i) *)
  (* 因为 H 给出 (A ⟪ v) i = lambda * v i *)
  (* 所以 Σ_j A_{ij} v_j = lambda * v i *)
  (* 因此 v_i * (Σ_j A_{ij} v_j) = v_i * (lambda * v_i) = lambda * v_i² *)
Admitted. (* 待证 *)

(* ===================================================================== *)
(* 8. 临时: 复用需要的 Axiom 列表                                       *)
(* ===================================================================== *)

(* R 有序域基本性质: x² ≥ 0 *)
Axiom R_sq_nonneg : forall x : R, x * x >= 0.

(* 有限和的正性: 若所有项 ≥ 0 且至少一项 > 0, 则和 > 0 *)
Axiom Rsum_pos_iff_exists_pos :
  forall (n : nat) (f : nat -> R),
    (forall k, Nat.lt k n -> f k >= 0) ->
    (exists k, Nat.lt k n /\ f k > 0) ->
    Rsum n f > 0.

(* 有限和: 若所有项 = 0, 则和 = 0 *)
Axiom Rsum_zero_iff_all_zero :
  forall (n : nat) (f : nat -> R),
    (forall k, Nat.lt k n -> f k = 0) ->
    Rsum n f = 0.

(* x > 0, y > 0 ⇒ x + y > 0 (lra 可证, 但为简化先列出) *)
Axiom R_pos_add : forall x y : R, x > 0 -> y > 0 -> x + y > 0.

(* x > 0, y > 0 ⇒ x * y > 0 *)
Axiom R_pos_mul : forall x y : R, x > 0 -> y > 0 -> x * y > 0.

(* x > 0 ⇒ x ≠ 0 *)
Axiom R_pos_nonzero : forall x : R, x > 0 -> x <> 0.

(* x * y > 0, y > 0 ⇒ x > 0 (除法原理) *)
Axiom R_div_pos : forall x y : R, y > 0 -> x * y > 0 -> x > 0.

(* ===================================================================== *)
(* 9. Phase 1 目标: 将 eigenvalue_positive_from_pd 改为 QED              *)
(* ===================================================================== *)

(* 重新声明主定理: 正定 ⇒ 特征值 > 0 *)
(* 这条将被 Phase 1 完全证明 *)

(* 目标形式: 矩阵在 n 维实向量空间, v 是 A 对应特征值 lambda 的特征向量, *)
(*           A 正定, v ≠ 0 ⇒ lambda > 0 *)

(* 完整证明路线:
   1. 由 Av = λv, 推出 quadratic_form A v = λ * norm_sq v
   2. 由 A 正定 + v ≠ 0, 推出 quadratic_form A v > 0
   3. 由 v ≠ 0, 推出 norm_sq v > 0
   4. 由 λ * norm_sq v > 0 且 norm_sq v > 0, 推出 λ > 0 *)

(* 步骤 1 已尝试: eigenvector_quadratic (Admitted) *)
(* 步骤 2: 展开 A 正定的定义 *)
(* 步骤 3: 已尝试: norm_sq_pos_iff_nonzero (Admitted) *)
(* 步骤 4: 由 R_div_pos 直接完成 *)

(* ===================================================================== *)
(* 10. 核心 QED 目标                                                     *)
(* ===================================================================== *)

Definition is_positive_definite (n : nat) (A : Matrix n) : Prop :=
  forall (x : nat -> R), (exists i, Nat.lt i n /\ x i <> 0) -> quadratic_form n A x > 0.

Theorem pd_implies_eigenvalue_positive :
forall (n : nat) (A : Matrix n) (lambda : R) (v : nat -> R),
    Nat.lt 0 n ->
    is_positive_definite n A ->
    (exists i : nat, Nat.lt i n /\ v i <> 0) ->
    (forall i : nat, Nat.lt i n -> (A ⟪ v) i = lambda * v i) ->
    lambda > 0.
Proof.
  intros n A lambda v Hn HPD Hv_nonzero Heq.
  (* 步骤 1: quadratic_form A v = lambda * norm_sq v *)
  (* 由 Heq: ∀i < n, (Av)_i = lambda * v_i *)
  (* 展开 quadratic_form n A v = Σ_i v_i * (Av)_i = Σ_i v_i * (lambda * v_i) *)
  unfold quadratic_form, inner_product, norm_sq.
  (* 这里需要精细的 rewrite, 暂用 admit *)
Admitted. (* Phase 1 完整 QED 化的关键位置 *)

(* ===================================================================== *)
(* 11. 备注                                                              *)
(* ===================================================================== *)
(* Phase 1 状态: 建立了内积/范数/矩阵-向量乘法/二次型基础设施,           *)
(*              但核心等式 (eigenvector_quadratic, norm_sq_pos_iff_nonzero)  *)
(*              和主定理 (pd_implies_eigenvalue_positive) 仍为 Admitted. *)
(*                                                                     *)
(* 阻塞原因:                                                            *)
(*   - Rsum_ext 对嵌套求和的处理                                       *)
(*   - admit 的 Rsum_split 未实现                                       *)
(*   - Rsum_pos_iff_exists_pos 等 Axiom 暂未补齐                       *)
(*                                                                     *)
(* 下一步:                                                              *)
(*   1. 实现 Rsum_split 为 Lemma                                       *)
(*   2. 补齐 Rsum 的 R_sq_nonneg 性质                                   *)
(*   3. 完成 eigenvector_quadratic, norm_sq_pos_iff_nonzero             *)
(*   4. 完成 pd_implies_eigenvalue_positive                              *)
(* ===================================================================== *)
