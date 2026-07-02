(* Equicontinuity.v *)
(* Stage 3: 等度连续谓词 + 模数函数 + 等度连续序列性质. *)
(* Reference: Rudin 1976, Principles of Mathematical Analysis, Ch. 7. *)

Require Import Reals.

From CompactEmbedding Require Import MetricCompact.

Open Scope R_scope.

(* ===================================================================== *)
(* 1. 等度连续 (equicontinuous family)                                    *)
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
(* 2. 模数函数 (modulus of continuity)                                    *)
(* ===================================================================== *)

Record ModulusOfContinuity (K : Rn -> Prop) (f : C0_on K) := mkModulus {
  mod_fn : R -> R;
  mod_pos : forall eps : R, eps > 0 -> mod_fn eps > 0;
  mod_cont : forall (eps : R) (x y : Rn),
    eps > 0 -> K x -> K y -> Rn_distance x y < mod_fn eps ->
      Rabs (proj1_sig f x - proj1_sig f y) < eps
}.

(* 等度连续的模数函数族: 对 F 中所有 f 共享同一个模数 *)
Definition common_modulus (K : Rn -> Prop) (F : C0_on K -> Prop) : Prop :=
  forall eps : R, eps > 0 ->
    exists delta : R, delta > 0 /\
      forall (f : C0_on K), F f ->
        forall (x y : Rn),
          K x -> K y -> Rn_distance x y < delta ->
          Rabs (proj1_sig f x - proj1_sig f y) < eps.

(* Equicontinuous 等价于有公共模数 *)
Lemma equicontinuous_iff_common_modulus (K : Rn -> Prop) (F : C0_on K -> Prop) :
  Equicontinuous K F <-> common_modulus K F.
Proof.
  unfold Equicontinuous, common_modulus; split; intros H; exact H.
Qed.

(* ===================================================================== *)
(* 3. 等度连续序列的逐点收敛                                              *)
(* ===================================================================== *)

Definition pointwise_limit (K : Rn -> Prop) (seq : nat -> C0_on K) (f : C0_on K) : Prop :=
  forall x : Rn, K x ->
    forall eps : R, eps > 0 ->
      exists N : nat, forall n : nat, (n >= N)%nat ->
        Rabs (proj1_sig (seq n) x - proj1_sig f x) < eps.

(* 等度连续 + 逐点收敛 => 一致收敛 *)
Lemma equicontinuous_pointwise_implies_uniform (K : Rn -> Prop) (seq : nat -> C0_on K) (f : C0_on K) :
  is_compact K ->
  Equicontinuous K (fun g => exists n : nat, g = seq n) ->
  pointwise_limit K seq f ->
  forall eps : R, eps > 0 ->
    exists N : nat, forall n : nat, (n >= N)%nat ->
      forall x : Rn, K x ->
        Rabs (proj1_sig (seq n) x - proj1_sig f x) < eps.
Proof.
  intros HK HEq Hlim eps Heps.
  admit.
Admitted.

(* ===================================================================== *)
(* 4. 总结                                                               *)
(* ===================================================================== *)
(* 交付: *)
(*   - Equicontinuous: 等度连续定义 *)
(*   - ModulusOfContinuity: 模数函数 Record *)
(*   - common_modulus: 公共模数 *)
(*   - equicontinuous_iff_common_modulus: 等价性 *)
(*   - pointwise_limit: 逐点收敛 *)
(*   - equicontinuous_pointwise_implies_uniform: 等度连续+逐点=>一致收敛 (Admitted) *)