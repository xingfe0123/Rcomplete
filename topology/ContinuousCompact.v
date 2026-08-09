(*
  ================================================================================
  ContinuousCompact.v — 连续映射保持紧性
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f: X → Y 连续，E ⊆ X 紧 ⟹ f(E) ⊆ Y 紧
 ================================================================================
*)

From Stdlib Require Import Reals Lra ClassicalEpsilon.

Open Scope R_scope.

(* ================================================================ *)
(*  度量空间                                                          *)
(* ================================================================ *)

Record MetricSpace : Type := mkMetricSpace {
  X : Type;
  d : X -> X -> R;
  d_nonneg : forall x y, 0 <= d x y;
  d_eq : forall x y, d x y = 0 <-> x = y;
  d_sym : forall x y, d x y = d y x;
  d_triangle : forall x y z, d x z <= d x y + d y z
}.

Definition ball {M : MetricSpace} (c : X M) (r : R) : X M -> Prop :=
  fun x => d M c x < r.

Definition OpenSet {M : MetricSpace} (U : X M -> Prop) : Prop :=
  forall x, U x -> exists r, r > 0 /\
    forall y, ball M x r y -> U y.

(* ================================================================ *)
(*  连续函数                                                          *)
(* ================================================================ *)

Definition ContinuousAt {M1 M2 : MetricSpace} (f : X M1 -> X M2) (p : X M1) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, d M1 p x < delta -> d M2 (f p) (f x) < eps.

Definition Continuous {M1 M2 : MetricSpace} (f : X M1 -> X M2) : Prop :=
  forall p, ContinuousAt f p.

(* ================================================================ *)
(*  像集与预像                                                        *)
(* ================================================================ *)

Definition Image {M1 M2 : MetricSpace} (f : X M1 -> X M2) (E : X M1 -> Prop) : X M2 -> Prop :=
  fun y => exists x, E x /\ f x = y.

Definition PreImage {M1 M2 : MetricSpace} (f : X M1 -> X M2) (V : X M2 -> Prop) : X M1 -> Prop :=
  fun x => V (f x).

(* ================================================================ *)
(*  紧性（用 nat + 上界 n 避免 Fin.t 导入冲突）                       *)
(* ================================================================ *)

Definition Cover {M : MetricSpace} (E : X M -> Prop) (F : (X M -> Prop) -> Prop) : Prop :=
  (forall U, F U -> OpenSet U) /\
  (forall x, E x -> exists U, F U /\ U x).

(* 紧性的定义：对任意开覆盖，存在 n 和 sigma : nat -> (X M -> Prop)，
   使得 i < n 时 sigma(i) ∈ F，且 E ⊆ ⋃_{i<n} sigma(i) *)
Definition Compact {M : MetricSpace} (E : X M -> Prop) : Prop :=
  forall F : (X M -> Prop) -> Prop, Cover E F ->
    exists (n : nat) (sigma : nat -> (X M -> Prop)),
      (forall i, (i < n)%nat -> F (sigma i)) /\
      (forall x, E x -> exists i, (i < n)%nat /\ sigma i x).

(* ================================================================ *)
(*  引理                                                              *)
(* ================================================================ *)

Lemma preimage_of_open_is_open : forall {M1 M2 : MetricSpace}
  (f : X M1 -> X M2) (V : X M2 -> Prop),
  Continuous f -> OpenSet V -> OpenSet (PreImage f V).
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
(*  主定理                                                            *)
(* ================================================================ *)

Theorem continuous_image_of_compact_is_compact :
  forall (M1 M2 : MetricSpace) (f : X M1 -> X M2) (E : X M1 -> Prop),
  Compact E ->
  Continuous f ->
  Compact (Image f E).
Proof.
  intros M1 M2 f E Hcomp Hcont.
  unfold Compact. intros F HcoverF.
  unfold Compact in Hcomp.
  set (G := fun U : X M1 -> Prop => exists V, F V /\ U = PreImage f V).
  assert (HG : Cover E G).
  { split.
    - intros U [V [HVF HUV]].
      rewrite HUV. apply preimage_of_open_is_open.
      + exact Hcont.
      + destruct HcoverF as [HFopen _]. apply HFopen. exact HVF.
    - intros x Hx.
      assert (Hfx : Image f E (f x)). { exists x. split. exact Hx. reflexivity. }
      destruct HcoverF as [_ HFcover].
      specialize (HFcover (f x) Hfx) as [V [HVF HVfx]].
      exists (PreImage f V).
      split.
      + exists V. auto.
      + exact HVfx.
  }
  specialize (Hcomp G HG) as [n [sigma [HGsub HGcover]]].
  (* 从 sigma(i) : G 提取对应的 V_i : F *)
  assert (Hex : forall i, (i < n)%nat ->
    exists V : X M2 -> Prop, F V /\ sigma i = PreImage f V).
  { intros i Hi. specialize (HGsub i Hi) as [V [HVF Hisigma]].
    exists V. auto. }
  (* 用 constructive choice 构造 select *)
  set (select := fun i : nat =>
    match lt_dec i n with
    | left Hi => proj1_sig (constructive_indefinite_description _ (Hex i Hi))
    | right _ => fun _ => True  (* _dummy，不会被使用 *)
    end).
  assert (HselectF : forall i, (i < n)%nat -> F (select i)).
  { intros i Hi. unfold select. destruct (lt_dec i n) as [Hi' | Hn].
    - destruct constructive_indefinite_description as [V [HVF _]]. exact HVF.
    - contradiction. }
  assert (HselectEq : forall i, (i < n)%nat -> sigma i = PreImage f (select i)).
  { intros i Hi. unfold select. destruct (lt_dec i n) as [Hi' | Hn].
    - destruct constructive_indefinite_description as [V [_ Heq]]. exact Heq.
    - contradiction. }
  exists n. exists select.
  split.
  - exact HselectF.
  - intros y Hy.
    destruct Hy as [x [Hx Hfxy]].
    specialize (HGcover x Hx) as [i [Hi Hsigmaix]].
    exists i. split.
    + exact Hi.
    + rewrite HselectEq. unfold PreImage.
      rewrite <- Hfxy. exact Hsigmaix.
Qed.
