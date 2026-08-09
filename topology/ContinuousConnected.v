(*
  ================================================================================
  ContinuousConnected.v — 连续映射保持连通性
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f: X → Y 连续，E ⊆ X 连通 ⟹ f(E) ⊆ Y 连通

  核心思路：反证法。假设 f(E) 不连通，则存在 Y 中开集 U,V 分离 f(E)。
  由 f 连续，f⁻¹(U), f⁻¹(V) 是 X 中开集，且分离 E，矛盾。
  ================================================================================
*)

From Stdlib Require Import Reals Lra ClassicalEpsilon.

Open Scope R_scope.

(* ================================================================ *)
(*  度量空间                                                          *)
(* ================================================================ *)

Record MetricSpace : Type := mkMetricSpace {
  MS : Type;
  d : MS -> MS -> R;
  d_nonneg : forall x y, 0 <= d x y;
  d_eq : forall x y, d x y = 0 <-> x = y;
  d_sym : forall x y, d x y = d y x;
  d_triangle : forall x y z, d x z <= d x y + d y z
}.

Definition ball (M : MetricSpace) (c : MS M) (r : R) : MS M -> Prop :=
  fun x => d M c x < r.

Definition OpenSet (M : MetricSpace) (U : MS M -> Prop) : Prop :=
  forall x, U x -> exists r, r > 0 /\
    forall y, ball M x r y -> U y.

(* ================================================================ *)
(*  连续函数                                                          *)
(* ================================================================ *)

Definition ContinuousAt (M1 M2 : MetricSpace) (f : MS M1 -> MS M2) (p : MS M1) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, d M1 p x < delta -> d M2 (f p) (f x) < eps.

Definition Continuous (M1 M2 : MetricSpace) (f : MS M1 -> MS M2) : Prop :=
  forall p, ContinuousAt M1 M2 f p.

(* ================================================================ *)
(*  像集与预像                                                        *)
(* ================================================================ *)

Definition Image (M1 M2 : MetricSpace) (f : MS M1 -> MS M2) (E : MS M1 -> Prop) : MS M2 -> Prop :=
  fun y => exists x, E x /\ f x = y.

Definition PreImage (M1 M2 : MetricSpace) (f : MS M1 -> MS M2) (V : MS M2 -> Prop) : MS M1 -> Prop :=
  fun x => V (f x).

(* ================================================================ *)
(*  连通性定义                                                        *)
(* ================================================================ *)

Definition Connected (M : MetricSpace) (E : MS M -> Prop) : Prop :=
  forall (U V : MS M -> Prop),
    OpenSet M U -> OpenSet M V ->
    (exists x, E x /\ U x) ->
    (exists x, E x /\ V x) ->
    (forall x, E x -> U x \/ V x) ->
    exists x, E x /\ U x /\ V x.

(* ================================================================ *)
(*  引理：连续映射下开集的原像是开集                                  *)
(* ================================================================ *)

Lemma preimage_of_open_is_open : forall (M1 M2 : MetricSpace)
  (f : MS M1 -> MS M2) (V : MS M2 -> Prop),
  Continuous M1 M2 f -> OpenSet M2 V -> OpenSet M1 (PreImage M1 M2 f V).
Proof.
  intros M1 M2 f V Hcont HV.
  unfold OpenSet. intros x Hx.
  specialize (HV (f x) Hx) as [r [Hr HVopen]].
  specialize (Hcont x r Hr) as [delta [delta_pos Hcd]].
  exists delta.
  split.
  - exact delta_pos.
  - intros y Hy. apply HVopen. apply Hcd. exact Hy.
Qed.

(* ================================================================ *)
(*  主定理：连续映射保持连通性                                        *)
(* ================================================================ *)

Theorem continuous_image_of_connected_is_connected :
  forall (M1 M2 : MetricSpace) (f : MS M1 -> MS M2) (E : MS M1 -> Prop),
  Continuous M1 M2 f ->
  Connected M1 E ->
  Connected M2 (Image M1 M2 f E).
Proof.
  intros M1 M2 f E Hcont Hconn.
  unfold Connected.
  intros U V HU HV HUf HVf Hcov.
  assert (HUE: exists x, E x /\ PreImage M1 M2 f U x).
  { destruct HUf as [y [HyImage HyU]].
    unfold Image in HyImage.
    destruct HyImage as [x [Hx Hfx]].
    exists x. split. exact Hx.
    unfold PreImage. rewrite Hfx. exact HyU.
  }
  assert (HVE: exists x, E x /\ PreImage M1 M2 f V x).
  { destruct HVf as [y [HyImage HyV]].
    unfold Image in HyImage.
    destruct HyImage as [x [Hx Hfx]].
    exists x. split. exact Hx.
    unfold PreImage. rewrite Hfx. exact HyV.
  }
  assert (HcovE: forall x, E x -> PreImage M1 M2 f U x \/ PreImage M1 M2 f V x).
  { intros x Hx. specialize (Hcov (f x)).
    assert (Hfx: Image M1 M2 f E (f x)).
    { exists x. split. exact Hx. reflexivity. }
    specialize (Hcov Hfx).
    destruct Hcov as [HUx|HVx].
    - left. exact HUx.
    - right. exact HVx.
  }
  assert (Hpre1: OpenSet M1 (PreImage M1 M2 f U)).
  { apply preimage_of_open_is_open. exact Hcont. exact HU. }
  assert (Hpre2: OpenSet M1 (PreImage M1 M2 f V)).
  { apply preimage_of_open_is_open. exact Hcont. exact HV. }
  specialize (Hconn (PreImage M1 M2 f U) (PreImage M1 M2 f V) Hpre1 Hpre2 HUE HVE HcovE) as [x [Hx [HUx HVx]]].
  exists (f x).
  split.
  - exists x. split. exact Hx. reflexivity.
  - split. exact HUx. exact HVx.
Qed.

Close Scope R_scope.
