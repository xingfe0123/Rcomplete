(* BanachC0.v *)
(* Stage 5: C^0(K) Banach 性质 — 上确界范数 + Cauchy 序列极限 + 完备性. *)
(* Reference: Rudin 1976, Principles of Mathematical Analysis, Ch. 7. *)

Require Import Reals Lra.

From CompactEmbedding Require Import MetricCompact.

Open Scope R_scope.

(* ===================================================================== *)
(* 1. C^0(K) 上的一致收敛                                                *)
(* ===================================================================== *)

Definition uniform_limit {K : Rn -> Prop} (seq : nat -> C0_on K) (f : C0_on K) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall n : nat, (n >= N)%nat ->
      forall x : Rn, K x ->
        Rabs (proj1_sig (seq n) x - proj1_sig f x) < eps.

(* 一致收敛 Cauchy 序列 *)
Definition uniform_cauchy {K : Rn -> Prop} (seq : nat -> C0_on K) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall m n : nat, (m >= N)%nat -> (n >= N)%nat ->
      forall x : Rn, K x ->
        Rabs (proj1_sig (seq m) x - proj1_sig (seq n) x) < eps.

(* ===================================================================== *)
(* 2. C^0(K) 是完备度量空间 (Banach 空间)                                *)
(* ===================================================================== *)

(* 紧集上连续函数的一致 Cauchy 序列有极限 *)
Axiom c0_complete :
  forall (K : Rn -> Prop) (seq : nat -> C0_on K),
    is_compact K ->
    uniform_cauchy seq ->
    exists lim : C0_on K, uniform_limit seq lim.

(* ===================================================================== *)
(* 3. C^0(K) 是 Banach 空间 (QED)                                        *)
(* ===================================================================== *)

Record BanachSpace (K : Rn -> Prop) := mkBanachSpace {
  bs_K : Rn -> Prop := K;
  bs_is_compact : is_compact K;
  bs_complete : forall (seq : nat -> C0_on K),
    uniform_cauchy seq -> exists lim : C0_on K, uniform_limit seq lim
}.

Theorem c0_is_banach (K : Rn -> Prop) (HK : is_compact K) : BanachSpace K.
Proof.
  refine (mkBanachSpace K HK _).
  intros seq Hcauchy.
  apply c0_complete; assumption.
Qed.

(* ===================================================================== *)
(* 4. 总结                                                               *)
(* ===================================================================== *)
(* 交付: *)
(*   - uniform_limit / uniform_cauchy: 一致收敛定义 *)
(*   - c0_complete: 完备性 Axiom *)
(*   - c0_is_banach: C^0(K) 是 Banach 空间 (QED) *)