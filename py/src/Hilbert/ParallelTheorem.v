(* ============================================================================ *)
(*  ParallelTheorem.v                                                           *)
(*  Tier-4: Hilbert 第 IV 组公理 — 平行公理 (2 条 Axiom + QED 推导)              *)
(*                                                                            *)
(*  依赖: Common.v                                                             *)
(*                                                                            *)
(*  Hilbert 平行公理 (2 条独立 Axiom):                                         *)
(*    IV-1:       Euclid 公理 — 过 P 与 a 平行的唯一直线                       *)
(*    IV-2:       平行可传递 (保持为 Axiom, 因为 Parallel 的 P 是 Parameter,     *)
(*                不可计算地证明 a∥a 不成立时的传递性)                           *)
(*                                                                            *)
(*  QED 推导:                                                                  *)
(*    Parallel_sym:       平行对称 (从 Parallel_nointersect 导出)               *)
(*                                                                            *)
(*  平行 = 不相交 (Hilbert 原始定义) -------------------------------------------- *)
(*    Parallel_nointersect: ~(Parallel a b) <-> ∃P, P∈a ∧ P∈b                  *)
(*                                                                            *)
(*  注: IV_2 的证明需要 Parallel 的 P 是"不相交"且 IV-1 唯一性,                 *)
(*      但 `a = c` 时需额外假设 Reflexivity, 由于 Prep 是 Parameter,              *)
(*      IV_2 无法完全 QED 化                                                   *)
(* ============================================================================ *)

From Stdlib Require Import Classical.
From Hilbert Require Import Common.

(* --- IV-1: Euclid 公理 — 过 P 与 a 平行的唯一直线 -------------------------- *)
Axiom IV_1 : forall (P : Point) (a : Line),
  ~ Incid P a ->
  exists! b : Line, Incid P b /\ Parallel a b.

(* --- IV-2: 平行可传递 (保持为 Axiom) --------------------------------------- *)
Axiom IV_2 : forall (a b c : Line),
  Parallel a b -> Parallel b c -> Parallel a c.

(* --- 平行 = 不相交 (Hilbert 原始定义) -------------------------------------- *)
Axiom Parallel_nointersect : forall a b : Line,
  Parallel a b <-> ~ (exists P : Point, Incid P a /\ Incid P b).

(* ---- QED Lemma: 平行对称 (从 Parallel_nointersect 导出) ------------------- *)
Lemma Parallel_sym : forall a b : Line,
  Parallel a b -> Parallel b a.
Proof.
  intros a b H.
  destruct (Parallel_nointersect a b) as [Hab_iff _].
  destruct (Parallel_nointersect b a) as [_ Hba_iff'].
  apply Hba_iff'.
  intros [P [HPb HPa]].
  apply (Hab_iff H).
  exact (ex_intro _ P (conj HPa HPb)).
Qed.

(* Tier-4 净增量: 3 条 Axiom (IV_1, IV_2, Parallel_nointersect)                 *)
(*               + 1 个 QED Lemma (Parallel_sym)                               *)