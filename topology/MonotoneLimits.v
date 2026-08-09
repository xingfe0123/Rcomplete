(*
  ================================================================================
  MonotoneLimits.v — 单调函数的单侧极限
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f: (a,b) → R 单调增 ⟹ ∀ x ∈ (a,b), f(x-) ≤ f(x) ≤ f(x+)
  ================================================================================
*)

From Stdlib Require Import Reals Lra ClassicalEpsilon.

Open Scope R_scope.

(* ================================================================ *)
(*  定义                                                              *)
(* ================================================================ *)

Definition monotone_inc (f : R -> R) (a b : R) : Prop :=
  forall x y, a < x < b -> a < y < b -> x < y -> f x <= f y.

(* 上确界性质 *)
Definition is_sup (S : R -> Prop) (m : R) : Prop :=
  (forall x, S x -> x <= m) /\
  (forall m', (forall x, S x -> x <= m') -> m <= m').

(* 下确界性质 *)
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

(* ================================================================ *)
(*  主定理                                                            *)
(* ================================================================ *)

(* 左极限：sup{f(y) : a < y < x} <= f(x) *)
Theorem monotone_left_limit_le :
  forall (f : R -> R) (a b x : R),
  monotone_inc f a b ->
  a < x < b ->
  forall s, is_sup (fun r => exists y, a < y < x /\ f y = r) s -> s <= f x.
Proof.
  intros f a b x Hmon Hx s Hs.
  unfold is_sup in Hs. destruct Hs as [Hup Hleast].
  apply Hleast. intros r [y [Hy Hfy]].
  rewrite <- Hfy.
  assert (Hyb: a < y < b). lra.
  apply Hmon. exact Hyb. lra. lra.
Qed.

(* 右极限：f(x) <= inf{f(y) : x < y < b} *)
Theorem monotone_right_limit_ge :
  forall (f : R -> R) (a b x : R),
  monotone_inc f a b ->
  a < x < b ->
  forall s, is_inf (fun r => exists y, x < y < b /\ f y = r) s -> f x <= s.
Proof.
  intros f a b x Hmon Hx s Hs.
  unfold is_inf in Hs. destruct Hs as [Hlo Hgeatest].
  apply Hgeatest. intros r [y [Hy Hfy]].
  rewrite <- Hfy.
  assert (Hya: a < y < b). lra.
  apply Hmon. lra. exact Hya. lra.
Qed.

(* 合并定理 *)
Theorem monotone_limits :
  forall (f : R -> R) (a b x : R),
  monotone_inc f a b ->
  a < x < b ->
  (forall s, is_sup (fun r => exists y, a < y < x /\ f y = r) s -> s <= f x) /\
  (forall s, is_inf (fun r => exists y, x < y < b /\ f y = r) s -> f x <= s).
Proof.
  intros f a b x Hmon Hx.
  split.
  - apply (@monotone_left_limit_le f a b x Hmon Hx).
  - apply (@monotone_right_limit_ge f a b x Hmon Hx).
Qed.

Close Scope R_scope.
