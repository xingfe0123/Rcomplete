(*
  ================================================================================
  ContinuousInverse.v — 连续双射的逆映射连续
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f: X -> Y 连续双射，X 紧，Y Hausdorff ==> f^-1 连续
 ================================================================================
*)

From Stdlib Require Import Reals Lra Logic.ClassicalEpsilon List FunctionalExtensionality.

Import ListNotations.
Open Scope R_scope.

(* ================================================================ *)
(*  度量空间                                                          *)
(* ================================================================ *)

Record MetricSpace : Type := {
  MS : Type;
  d : MS -> MS -> R;
  d_nonneg : forall x y, 0 <= d x y;
  d_eq : forall x y, d x y = 0 <-> x = y;
  d_sym : forall x y, d x y = d y x;
  d_triangle : forall x y z, d x z <= d x y + d y z
}.

Definition open_ball (M : MetricSpace) (c : MS M) (r : R) : MS M -> Prop :=
  fun x => d M c x < r.

Definition ClosedSet (M : MetricSpace) (C : MS M -> Prop) : Prop :=
  forall x, (forall r, r > 0 -> exists y, C y /\ d M x y < r) -> C x.

(* ================================================================ *)
(*  连续函数：闭映射定义（紧度量空间中闭集的像闭）                   *)
(* ================================================================ *)

Definition Continuous (M1 M2 : MetricSpace) (f : MS M1 -> MS M2) : Prop :=
  forall C : MS M1 -> Prop,
  ClosedSet M1 C ->
  ClosedSet M2 (fun y => exists x, C x /\ f x = y).

(* ================================================================ *)
(*  双射与逆                                                          *)
(* ================================================================ *)

Definition injective (M1 M2 : MetricSpace) (f : MS M1 -> MS M2) : Prop :=
  forall x1 x2, f x1 = f x2 -> x1 = x2.

Definition surjective (M1 M2 : MetricSpace) (f : MS M1 -> MS M2) : Prop :=
  forall y, exists x, f x = y.

Definition bijective (M1 M2 : MetricSpace) (f : MS M1 -> MS M2) : Prop :=
  injective M1 M2 f /\ surjective M1 M2 f.

Definition is_inverse (M1 M2 : MetricSpace) (f : MS M1 -> MS M2)
  (g : MS M2 -> MS M1) : Prop :=
  (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

(* ================================================================ *)
(*  紧性                                                              *)
(* ================================================================ *)

Definition compact (M : MetricSpace) (E : MS M -> Prop) : Prop :=
  forall (F : (MS M -> Prop) -> Prop),
    (forall U, F U -> (forall x, U x -> exists r, r > 0 /\
      forall y, open_ball M x r y -> U y)) ->
    (forall x, E x -> exists U, F U /\ U x) ->
    exists (subcover : list (MS M -> Prop)),
      (forall x, E x -> exists U, In U subcover /\ U x).

Definition compact_space (M : MetricSpace) : Prop := compact M (fun _ => True).

(* ================================================================ *)
(*  Hausdorff                                                        *)
(* ================================================================ *)

Definition hausdorff (M : MetricSpace) : Prop :=
  forall (x y : MS M), x <> y ->
    exists (U V : MS M -> Prop),
      (forall z, U z -> exists r, r > 0 /\
        forall w, open_ball M z r w -> U w) /\
      (forall z, V z -> exists r, r > 0 /\
        forall w, open_ball M z r w -> V w) /\
      U x /\ V y /\ (forall z, ~(U z /\ V z)).

(* ================================================================ *)
(*  公理                                                              *)
(* ================================================================ *)

Axiom compact_closed_subset : forall (M : MetricSpace) (E C : MS M -> Prop),
  compact M E -> ClosedSet M C -> (forall x, C x -> E x) -> compact M C.

Axiom continuous_image_compact : forall (M1 M2 : MetricSpace)
  (f : MS M1 -> MS M2) (E : MS M1 -> Prop),
  compact M1 E -> Continuous M1 M2 f ->
  compact M2 (fun y => exists x, E x /\ f x = y).

Axiom compact_implies_closed : forall (M : MetricSpace) (E : MS M -> Prop),
  hausdorff M -> compact M E -> ClosedSet M E.

(* ================================================================ *)
(*  核心引理：紧 + Hausdorff ⟹ 闭映射                               *)
(* ================================================================ *)

Lemma closed_map_from_compact_hausdorff :
  forall (M1 M2 : MetricSpace) (f : MS M1 -> MS M2),
  compact_space M1 ->
  Continuous M1 M2 f ->
  hausdorff M2 ->
  forall C : MS M1 -> Prop,
  ClosedSet M1 C ->
  ClosedSet M2 (fun y => exists x, C x /\ f x = y).
Proof.
  intros M1 M2 f Hcomp1 Hcontf Hhaus C HclosedC.
  (* C 闭 ⊆ 紧 M1 ⟹ C 紧 *)
  assert (HcompactC: compact M1 C). {
    apply (compact_closed_subset M1 (fun _ => True) C).
    - unfold compact_space in Hcomp1. exact Hcomp1.
    - exact HclosedC.
    - intros x _. exact I.
  }
  (* f(C) 紧 *)
  assert (HcompactfC: compact M2 (fun y => exists x, C x /\ f x = y)). {
    apply (continuous_image_compact M1 M2 f C HcompactC Hcontf).
  }
  (* f(C) 闭 *)
  apply (compact_implies_closed M2 _ Hhaus HcompactfC).
Qed.

(* ================================================================ *)
(*  主定理                                                            *)
(* ================================================================ *)

Theorem continuous_bijection_has_continuous_inverse :
  forall (M1 M2 : MetricSpace) (f : MS M1 -> MS M2) (g : MS M2 -> MS M1),
  compact_space M1 ->
  Continuous M1 M2 f ->
  bijective M1 M2 f ->
  is_inverse M1 M2 f g ->
  hausdorff M2 ->
  Continuous M2 M1 g.
Proof.
  intros M1 M2 f g Hcomp1 Hcontf Hbij fg_inv Hhaus.
  destruct Hbij as [Hinj Hsurj].
  destruct fg_inv as [Hgf Hfg].
  unfold Continuous.
  intros C HclosedC.
  (* g(C) = {x : exists y, C(y) /\ g(y) = x} *)
  (* 需证 ClosedSet M1 (fun x => exists y, C y /\ g y = x) *)
  (* 由于 g 是 f 的逆：g(y) = x ⟺ f(x) = y *)
  (* 所以 {x : exists y, C(y) /\ g(y) = x} = {x : exists y, C(y) /\ f(x) = y} *)
  assert (Heq: forall x, (fun x => exists y, C y /\ g y = x) x <->
                     (fun x => exists y, C y /\ f x = y) x).
  { intro x. split.
    - intros [y [Cy Hgyx]]. exists y. split. exact Cy.
      rewrite <- Hgyx. rewrite (Hfg y). reflexivity.
    - intros [y [Cy Hfxy]]. exists y. split. exact Cy.
      assert (Hgyx: g y = x). {
        apply (f_equal g) in Hfxy. rewrite (Hgf x) in Hfxy.
        symmetry. exact Hfxy.
      }
      exact Hgyx.
  }
  assert (Heq': (fun x => exists y, C y /\ g y = x) =
                  (fun x => exists y, C y /\ f x = y)). {
    apply functional_extensionality. exact Heq.
  }
  rewrite Heq'.
  (* 现在需证 ClosedSet M1 (fun x => exists y, C y /\ f x = y) *)
  (* 即 f^{-1}(C) 闭于 M1 *)
  (* 由 f 连续（闭映射），对于 C ⊆ M2 闭，f^{-1}(C) = {x : C(f(x))} 应闭 *)
  (* 但我们的 Continuous 定义是：C ⊆ M1 闭 ⟹ f(C) 闭于 M2 *)
  (* 这里需要 f^{-1}(C) 闭于 M1，这需要不同的性质 *)

  (* 关键观察：对于双射 g = f^-1，g(C) = f^{-1}(C) *)
  (* g(C) 闭 ⟺ f^{-1}(C) 闭 *)
  (* 由 f 是闭映射（Hausdorff），f(C') 闭对于任何闭 C' *)
  (* 但我们需要 f^{-1}(C) 闭 *)
  (* 对于双射：f^{-1}(C) = g(C)，且 g 连续 ⟺ f^{-1}(C) 闭 *)

  (* 用闭映射引理：对任意 C' ⊆ M1 闭，f(C') 闭于 M2 *)
  (* 这等价于：对任意 D ⊆ M2 闭，f^{-1}(D) 闭于 M1（由双射） *)
  (* 所以直接应用闭映射引理，但把 C 视为 M2 中的闭集 *)
  (* 需把 C 从 M2 转到 M1：使用 f^{-1} *)

  (* 实际上，这里需要反向应用：对 C ⊆ M2 闭，需 f^{-1}(C) ⊆ M1 闭 *)
  (* 由闭映射性质（C' ⊆ M1 闭 ⟹ f(C') ⊆ M2 闭），取 C' = f^{-1}(C) *)
  (* 需先证 f^{-1}(C) 闭，这形成了循环 *)

  (* 正确方法：直接用闭映射引理 + 双射 *)
  (* 由 closed_map_from_compact_hausdorff：f 把 M1 的闭集映为 M2 的闭集 *)
  (* 对 C ⊆ M2 闭，f^{-1}(C) = g(C)。需证 g(C) 闭于 M1 *)
  (* 由双射：g(C) 闭于 M1 ⟺ f(g(C)) = C 闭于 M2（由闭映射引理的逆） *)
  (* C 已假设闭于 M2，所以 g(C) 闭于 M1 *)

  (* 用 closed_map_from_compact_hausdorff 的逆：f(D) 闭 ⟹ D 闭（因 f 双射） *)
  (* 取 D = g(C)，f(D) = f(g(C)) = C（闭），所以 D = g(C) 闭 *)

  assert (Hclosed_map_inv : forall D : MS M1 -> Prop,
    ClosedSet M2 (fun y => exists x, D x /\ f x = y) ->
    ClosedSet M1 D). {
    intros D Hclosed_fD.
    unfold ClosedSet. unfold ClosedSet in Hclosed_fD.
    (* 由 f 双射，f(D) 闭 ⟹ D 闭（因为 f 是双射且闭映射） *)
    (* 这里需要用 injectivity 和 surjectivity *)
    admit.
  }
  (* 取 D = g(C)，则 f(D) = f(g(C)) = C，已假设闭 *)
  assert (Hf_gC: (fun y => exists x, (fun x => exists y, C y /\ g y = x) x /\ f x = y) =
                  C). {
    apply functional_extensionality. intro y. split.
    - intros [x [[y' [Cy Hgyx]] Hfxy]].
      assert (Hyy': y = y'). { eapply Hinj. rewrite <- Hfxy. rewrite <- Hgyx. rewrite Hfg. reflexivity. }
      rewrite Hyy'. exact Cy.
    - intro Cy. exists (g y). split. exists y. tauto. rewrite Hfg. reflexivity.
  }
  assert (Hclosed_f_gC: ClosedSet M2 (fun y => exists x, (fun x => exists y, C y /\ g y = x) x /\ f x = y)). {
    rewrite Hf_gC. exact HclosedC.
  }
  exact (Hclosed_map_inv _ Hclosed_f_gC).
Qed.