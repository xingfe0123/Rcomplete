From Stdlib Require Import Reals RIneq Ranalysis.
From Stdlib Require Import ClassicalEpsilon.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import ProofIrrelevance.

Open Scope R_scope.

(******************************************************************************)
(* 度量空间定义                                                                *)
(******************************************************************************)

Record MetricSpace : Type := {
  X :> Type;
  dist : X -> X -> R;
  dist_self : forall x, dist x x = 0;
  dist_sym : forall x y, dist x y = dist y x;
  dist_triangle : forall x y z, dist x z <= dist x y + dist y z;
  dist_eq_ident : forall x y, dist x y = 0 -> x = y
}.

(******************************************************************************)
(* 序列收敛的 ε-N 定义                                                         *)
(******************************************************************************)

Definition convergent (ms : MetricSpace) (p : nat -> ms) (p0 : ms) : Prop :=
  forall eps : R, eps > 0 ->
    exists N : nat, forall n : nat, N <= n -> dist (p n) p0 < eps.

(******************************************************************************)
(* 邻域定义                                                                   *)
(******************************************************************************)

Definition open_ball (ms : MetricSpace) (p : ms) (r : R) (q : ms) : Prop :=
  dist q p < r.

Definition neighborhood (ms : MetricSpace) (p : ms) (U : ms -> Prop) : Prop :=
  exists r : R, r > 0 /\ forall q : ms, open_ball p r q -> U q.

(******************************************************************************)
(* "除有限项外所有" 定义                                                       *)
(******************************************************************************)

Definition all_but_finitely_many (ms : MetricSpace) (p : nat -> ms) (P : ms -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P (p n).

(******************************************************************************)
(* 定理：收敛 ⟺ 每个邻域包含除有限项外的所有项                                    *)
(******************************************************************************)

Theorem convergent_iff_neighborhood :
  forall (ms : MetricSpace) (p : nat -> ms) (p0 : ms),
    convergent p p0 <-> forall U : ms -> Prop, neighborhood p0 U -> all_but_finitely_many p U.

Proof.
  split.
  - (* => 方向：收敛 => 每个邻域包含除有限项外的所有项 *)
    intros Hconv U [r [Hr HrU]].
    unfold convergent in Hconv.
    specialize (Hconv r Hr) as [N HN].
    exists N.
    intros n Hn.
    apply HrU.
    apply HN.
    apply Hn.
  - (* <= 方向：每个邻域包含除有限项外的所有项 => 收敛 *)
    intros Hnei eps Heps.
    specialize (Hnei (open_ball p0 eps)).
    assert (Hnb : neighborhood p0 (open_ball p0 eps)).
    { exists eps. split. apply Heps. intros q Hq. apply Hq. }
    specialize (Hnei Hnb).
    destruct Hnei as [N HN].
    exists N.
    intros n Hn.
    apply HN.
    apply Hn.
Qed.
