(*
  ================================================================================
  MonotoneDiscontinuities.v — 单调函数的间断点可数
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f: (a,b) → R 单调 ⟹ f 的间断点集可数
  ================================================================================
*)

From Stdlib Require Import Reals Lra ClassicalEpsilon Ensembles.

Open Scope R_scope.

(* ================================================================ *)
(*  定义                                                              *)
(* ================================================================ *)

Definition monotone_inc (f : R -> R) (a b : R) : Prop :=
  forall x y, a < x < b -> a < y < b -> x < y -> f x <= f y.

Definition monotone_dec (f : R -> R) (a b : R) : Prop :=
  forall x y, a < x < b -> a < y < b -> x < y -> f y <= f x.

Definition monotone (f : R -> R) (a b : R) : Prop :=
  monotone_inc f a b \/ monotone_dec f a b.

(* 上确界 *)
Definition is_sup (S : R -> Prop) (m : R) : Prop :=
  (forall x, S x -> x <= m) /\
  (forall m', (forall x, S x -> x <= m') -> m <= m').

(* 下确界 *)
Definition is_inf (S : R -> Prop) (m : R) : Prop :=
  (forall x, S x -> m <= x) /\
  (forall m', (forall x, S x -> m' <= x) -> m' <= m).

(* 完备性公理 *)
Axiom completeness_sup : forall (S : R -> Prop),
  (exists x, S x) -> (exists m, forall x, S x -> x <= m) ->
  { m : R | is_sup S m }.

Axiom completeness_inf : forall (S : R -> Prop),
  (exists x, S x) -> (exists m, forall x, S x -> m <= x) ->
  { m : R | is_inf S m }.

(* 间断点：sup{f(y) : a < y < x} < inf{f(y) : x < y < b} *)
Definition is_discontinuity (f : R -> R) (a b x : R) : Prop :=
  forall s t,
    is_sup (fun r => exists y, a < y < x /\ f y = r) s ->
    is_inf (fun r => exists y, x < y < b /\ f y = r) t ->
    s < t.

(* f 和 -f 有相同的间断点 *)
Lemma discontinuity_equiv :
  forall (f : R -> R) (a b x : R),
  a < x < b ->
  is_discontinuity f a b x ->
  is_discontinuity (fun z => -f z) a b x.
Proof.
  intros f a b x Hx H.
  unfold is_discontinuity.
  intros s t Hs Ht.
  (* 需要将 is_sup (fun r => -f y = r) 转化为 is_sup (fun r => f y = r) *)
Admitted.

(* 可数：存在到 nat 的单射 *)
Definition injective {X Y : Type} (f : X -> Y) : Prop :=
  forall x1 x2, f x1 = f x2 -> x1 = x2.

Definition countable (X : Type) : Prop :=
  exists f : X -> nat, injective f.

(* 间断点集可数 *)
Definition discontinuities_countable (f : R -> R) (a b : R) : Prop :=
  countable {x : R | a < x < b /\ is_discontinuity f a b x}.

(* ================================================================ *)
(*  辅助引理                                                          *)
(* ================================================================ *)

(* 跳跃区间互不相交 *)
Lemma disjoint_jumps :
  forall (f : R -> R) (a b : R),
  monotone_inc f a b ->
  forall x y, a < x -> x < y -> y < b ->
    is_discontinuity f a b x -> is_discontinuity f a b y ->
    forall s t u v,
      is_sup (fun r => exists z, a < z < x /\ f z = r) s ->
      is_inf (fun r => exists z, x < z < b /\ f z = r) t ->
      is_sup (fun r => exists z, a < z < y /\ f z = r) u ->
      is_inf (fun r => exists z, y < z < b /\ f z = r) v ->
      t <= u.
Proof.
  intros f a b Hmon x y Hax Hxy Hyb Hdisc_x Hdisc_y s t u v Hs Ht Hu Hv.
  assert (Hmon2: forall z1 z2, a < z1 < b -> a < z2 < b -> z1 < z2 -> f z1 <= f z2).
  { exact Hmon. }
  (* 对任意 z ∈ (x, y)，有 f(z) ≤ u（因为 u 是 {f(w) : a < w < y} 的上确界） *)
  assert (Hle: forall z, x < z < y -> f z <= u).
  { intros z Hz. apply Hu. exists z. split. lra. reflexivity. }
  (* 对任意 z ∈ (x, y)，有 t ≤ f(z)（因为 t 是 {f(w) : x < w < b} 的下确界） *)
  assert (Hge: forall z, x < z < y -> t <= f z).
  { intros z Hz. apply Ht. exists z. split. lra. reflexivity. }
  (* 故 t ≤ f(z) ≤ u 对所有 z ∈ (x, y) 成立 *)
  assert (Hmid: forall z, x < z < y -> t <= u).
  { intros z Hz. specialize (Hge z Hz). specialize (Hle z Hz). lra. }
  assert (Hxz0: x < (x + y) / 2). lra.
  assert (Hz0y: (x + y) / 2 < y). lra.
  specialize (Hmid ((x + y) / 2) (conj Hxz0 Hz0y)).
  lra.
Admitted.

(* ================================================================ *)
(*  主定理                                                            *)
(* ================================================================ *)

Theorem monotone_inc_discontinuities_countable :
  forall (f : R -> R) (a b : R),
  monotone_inc f a b ->
  discontinuities_countable f a b.
Proof.
  intros f a b Hmon.
  unfold discontinuities_countable.
  (* 构造从间断点集到 Q 的单射 *)
  (* 对每个间断点 x，跳跃 (f(x⁻), f(x⁺)) 是开区间 *)
  (* 由 Q 在 R 中稠密，存在唯一有理数 q_x ∈ (f(x⁻), f(x⁺)) *)
  (* 映射 x ↦ q_x 是单射（因跳跃区间互不相交） *)
  admit.
Admitted.

Theorem monotone_discontinuities_countable :
  forall (f : R -> R) (a b : R),
  monotone f a b ->
  discontinuities_countable f a b.
Proof.
  intros f a b Hmon.
  destruct Hmon as [Hinc|Hdec].
  - apply monotone_inc_discontinuities_countable. exact Hinc.
  - assert (Hmono_inc: monotone_inc (fun x => -f x) a b).
    { unfold monotone_inc. intros x0 y0 Hx0 Hy0 Hlt. specialize (Hdec x0 y0 Hx0 Hy0 Hlt). lra. }
    assert (Hcount: discontinuities_countable (fun x => -f x) a b).
    { apply monotone_inc_discontinuities_countable. exact Hmono_inc. }
    unfold discontinuities_countable in Hcount.
    unfold countable in Hcount.
    destruct Hcount as [g Hinj].
    (* 由于 f 和 -f 有相同的间断点集（由 discontinuity_equiv），g 也是 f 的间断点集到 nat 的单射 *)
    assert (Hdisc_same: {x | a < x < b /\ is_discontinuity f a b x} = {x | a < x < b /\ is_discontinuity (fun z => -f z) a b x}).
    { admit. }
    destruct Hdisc_same.
    exists g. exact Hinj.
Admitted.

Close Scope R_scope.
