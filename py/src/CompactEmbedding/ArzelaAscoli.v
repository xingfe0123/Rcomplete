(* ArzelaAscoli.v *)
(* Arzela-Ascoli Theorem: equicontinuous + uniformly bounded *)
(* family of continuous functions on a compact set is relatively compact. *)
(* Reference: Arzela 1882, Ascoli 1883, Rudin 1976. *)

Require Import Reals Lra.

From CompactEmbedding Require Import MetricCompact.

Open Scope R_scope.
(* Set Implicit Arguments *)

(* ===================================================================== *)
(* 1. Uniformly Bounded Family                                            *)
(* ===================================================================== *)

Definition UniformlyBounded (K : Rn -> Prop) (F : C0_on K -> Prop) : Prop :=
  exists M : R, M > 0 /\
    forall (f : C0_on K),
      F f ->
      forall (x : Rn),
        K x ->
        Rabs (proj1_sig f x) <= M.

(* ===================================================================== *)
(* 2. Equicontinuous Family (Section 风格避免类型推断)                     *)
(* ===================================================================== *)

Definition Equicontinuous (K : Rn -> Prop) (F : C0_on K -> Prop) : Prop :=
  forall eps : R, eps > 0 ->
    exists delta : R, delta > 0 /\
      forall (f : C0_on K),
        F f ->
        forall (x y : Rn),
          K x -> K y -> Rn_distance x y < delta ->
          Rabs (proj1_sig f x - proj1_sig f y) < eps.

(* ===================================================================== *)
(* 3. Relative Compactness: sequence version                              *)
(* ===================================================================== *)

Definition RelativelyCompact_seq (K : Rn -> Prop) (F : C0_on K -> Prop) : Prop :=
  forall (seq : nat -> C0_on K),
    (forall n : nat, F (seq n)) ->
    exists (subseq : nat -> nat),
      Strictly_Increasing subseq /\
      exists lim : C0_on K,
        forall eps : R, eps > 0 ->
          exists N : nat,
            forall k : nat,
              (N <= k)%nat ->
              forall x : Rn,
                K x ->
                Rabs (proj1_sig (seq (subseq k)) x - proj1_sig lim x) < eps.

(* ===================================================================== *)
(* 4. Arzela-Ascoli Theorem (主定理 - 完整证明结构)                        *)
(* ===================================================================== *)
(* 证明策略:
   1. 紧集 K ⊆ R^n 可分: 存在可数稠密集 D
   2. 对角线法: 从 {f_n} 提取子列, 在 D 上逐点收敛
   3. 等度连续 → 一致收敛: 点态收敛 + 等度连续 ⇒ 一致收敛
   4. 极限函数连续 (等度连续 + 一致有界)
*)

Section ArzelaAscoliTheorem.
  Variable K : Rn -> Prop.
  Hypothesis HK : is_compact K.
  Variable F : C0_on K -> Prop.
  Hypothesis HEq : @Equicontinuous K F.
  Hypothesis HBd : UniformlyBounded K F.

  (* ----------------------------------------------------- *)
  (* Lemma 1: 紧集可分 (在 R^n 中)                          *)
  (* ----------------------------------------------------- *)
  (* K ⊆ R^n 紧 ⇒ K 有可数稠密集 *)
  (* 构造: 对每 m∈ℕ, 用半径 1/m 的有限球覆盖 K, 取球心 *)
  Lemma compact_separable :
    exists (D : nat -> Rn),
      forall (x : Rn) (eps : R),
        K x -> eps > 0 ->
        exists (n : nat) (y : Rn),
          D n = y /\ Rn_distance x y < eps.
  Proof.
    admit.
  Admitted.

  (* ----------------------------------------------------- *)
  (* Lemma 2: 对角线提取 + 点态极限构造                        *)
  (* ----------------------------------------------------- *)
  (* 给定序列 seq : nat -> C0_on K,
     存在子列使得在每点 x ∈ K 收敛 *)
  Lemma subseq_with_pointwise_limit (seq : nat -> C0_on K) :
    (forall n : nat, F (seq n)) ->
    exists (subseq : nat -> nat) (f : Rn -> R),
      Strictly_Increasing subseq /\
      ContinuousOn f K /\
      forall (x : Rn) (eps : R),
        K x -> eps > 0 ->
        exists N : nat, forall k : nat,
          (N <= k)%nat ->
          Rabs (proj1_sig (seq (subseq k)) x - f x) < eps.
  Proof.
    admit.
  Admitted.

  (* ----------------------------------------------------- *)
  (* Lemma 3: 等度连续 + 点态收敛 → 一致收敛                 *)
  (* ----------------------------------------------------- *)
  Lemma equicontinuous_uniform_limit
    (seq : nat -> C0_on K) (f : C0_on K) :
    (forall n : nat, F (seq n)) ->
    (forall (x : Rn) (eps : R),
      K x -> eps > 0 ->
      exists N : nat, forall k : nat,
        (N <= k)%nat ->
        Rabs (proj1_sig (seq k) x - proj1_sig f x) < eps) ->
    forall eps : R, eps > 0 ->
      exists N : nat, forall k : nat,
        (N <= k)%nat -> forall x : Rn,
          K x ->
          Rabs (proj1_sig (seq k) x - proj1_sig f x) < eps.
  Proof.
    admit.
  Admitted.

  (* ----------------------------------------------------- *)
  (* Lemma 4: 等度连续极限函数连续 (简化)                     *)
  (* ----------------------------------------------------- *)
  (* 从等度连续族中提取的逐点收敛子列, 其极限函数一致连续 *)
  Lemma equicontinuous_limit_is_continuous
    (seq : nat -> C0_on K) (f : Rn -> R) :
    (forall n : nat, F (seq n)) ->
    (forall (x : Rn) (eps : R),
      K x -> eps > 0 ->
      exists N : nat, forall k : nat,
        (N <= k)%nat ->
        Rabs (proj1_sig (seq k) x - f x) < eps) ->
    ContinuousOn f K.
  Proof. Admitted.

  (* ----------------------------------------------------- *)
  (* 主定理证明                                             *)
  (* ----------------------------------------------------- *)
  Theorem arzela_ascoli_theorem :
    RelativelyCompact_seq K F.
  Proof.
    intros seq Hseq.
    destruct compact_separable as [D HDense].
    destruct (subseq_with_pointwise_limit seq Hseq) as [subseq [f [Hincr [Hcont Hpoint]]]].
    exists subseq. split. exact Hincr.
    exists (exist _ f Hcont).
    (* 证明一致收敛: 等度连续 + 紧致性 → 一致收敛 *)
    admit.
  Admitted.

End ArzelaAscoliTheorem.

(* ===================================================================== *)
(* 5. Corollary: 序列版本 (从主定理推导)                                    *)
(* ===================================================================== *)

Corollary arzela_ascoli_sequence :
  forall (K : Rn -> Prop),
    is_compact K ->
    forall (seq : nat -> C0_on K),
      (forall eps : R, eps > 0 ->
        exists delta : R, delta > 0 /\
          forall (n : nat) (x y : Rn),
            K x -> K y -> Rn_distance x y < delta ->
            Rabs (proj1_sig (seq n) x - proj1_sig (seq n) y) < eps) ->
      (exists M : R, M > 0 /\
        forall (n : nat) (x : Rn), K x -> Rabs (proj1_sig (seq n) x) <= M) ->
      exists (subseq : nat -> nat),
        Strictly_Increasing subseq /\
        exists lim : C0_on K,
          forall eps : R, eps > 0 ->
            exists N : nat,
              forall k : nat,
                (N <= k)%nat ->
                forall x : Rn,
                  K x ->
                  Rabs (proj1_sig (seq (subseq k)) x - proj1_sig lim x) < eps.
Proof.
  intros K HK seq Heq Hbound.
  set (F := fun f : C0_on K => exists n : nat, f = seq n).
  destruct Hbound as [M [HM Hbound']].
  assert (HF_bound : UniformlyBounded K F).
  { exists M. split. exact HM. intros f [n Hn] x Kx. subst f. exact (Hbound' n x Kx). }
  assert (HF_eq : @Equicontinuous K F).
  { intros eps Heps. specialize (Heq eps Heps) as [delta [Hdelta Hdelta']]. exists delta. split. exact Hdelta. intros f [n Hn] x y Kx Ky Hdist. subst f. exact (Hdelta' n x y Kx Ky Hdist). }
  assert (HF_seq : forall n : nat, F (seq n)).
  { intros n. exists n. reflexivity. }
  destruct (arzela_ascoli_theorem K HK F HF_eq HF_bound seq HF_seq) as [subseq [Hsubseq [lim Hconv]]].
  exists subseq; split; [exact Hsubseq | exists lim; exact Hconv].
Admitted.

(* ===================================================================== *)
(* 6. Summary                                                            *)
(* ===================================================================== *)
(* Arzela-Ascoli 定理已完全形式化为精确命题:
   - UniformlyBounded: Definition (一致有界)
   - Equicontinuous: Definition (等度连续, Section 风格)
   - RelativelyCompact_seq: Definition (序列版本的相对紧性)
   - arzela_ascoli_theorem: Theorem (主定理, honest Admitted)
   - arzela_ascoli_sequence: Corollary (从主定理推导)
   QED 缺口: 需要紧度量空间的可分性 + 对角线论证 + 等度连续→一致收敛 *)