(*
  ================================================================================
  MonotoneNoSecondKind.v — 单调函数没有第二类间断点
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f: (a,b) → R 单调 ⟹ f 没有第二类间断点
  ================================================================================
*)

From Stdlib Require Import Reals Lra ClassicalEpsilon.

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

Definition left_limit_exists (f : R -> R) (a b x : R) : Prop :=
  exists l : R, forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall y, a < y < x -> Rabs (x - y) < delta -> Rabs (f y - l) < eps.

Definition right_limit_exists (f : R -> R) (a b x : R) : Prop :=
  exists l : R, forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall y, x < y < b -> Rabs (x - y) < delta -> Rabs (f y - l) < eps.

Definition no_second_kind_discontinuity (f : R -> R) (a b : R) : Prop :=
  forall x, a < x < b -> left_limit_exists f a b x /\ right_limit_exists f a b x.

(* 上确界性质 *)
Definition is_sup (S : R -> Prop) (m : R) : Prop :=
  (forall x, S x -> x <= m) /\
  (forall m', (forall x, S x -> x <= m') -> m <= m').

(* 下确界性质 *)
Definition is_inf (S : R -> Prop) (m : R) : Prop :=
  (forall x, S x -> m <= x) /\
  (forall m', (forall x, S x -> m' <= x) -> m' <= m).

Axiom completeness_sup : forall (S : R -> Prop),
  (exists x, S x) -> (exists m, forall x, S x -> x <= m) ->
  { m : R | is_sup S m }.

Axiom completeness_inf : forall (S : R -> Prop),
  (exists x, S x) -> (exists m, forall x, S x -> m <= x) ->
  { m : R | is_inf S m }.

(* ================================================================ *)
(*  辅助引理                                                          *)
(* ================================================================ *)

(* 若 s = sup S 且 s - eps < s，则存在 y 使得 y ∈ S 且 y > s - eps *)
Lemma sup_adherent :
  forall (S : R -> Prop) (s : R),
  is_sup S s ->
  forall eps, eps > 0 ->
  exists x, S x /\ s - eps < x.
Proof.
  intros S s Hs eps Heps.
  unfold is_sup in Hs.
  destruct Hs as [Hup Hleast].
  assert (H: ~ (forall x, S x -> x <= s - eps)).
  { intro Hcontra.
    apply Hleast in Hcontra.
    lra.
  }
  (* 由 ¬(∀x, Sx → x ≤ s-ε)，存在 x 使得 Sx ∧ x > s-ε *)
  apply not_all_ex_not in H.
  destruct H as [x Hx].
  exists x.
  split.
  - apply not_imply_elim in Hx. exact Hx.
  - apply not_imply_elim2 in Hx. lra.
Qed.

(* 若 s = inf S 且 s + eps > s，则存在 y 使得 y ∈ S 且 y < s + eps *)
Lemma inf_adherent :
  forall (S : R -> Prop) (s : R),
  is_inf S s ->
  forall eps, eps > 0 ->
  exists x, S x /\ x < s + eps.
Proof.
  intros S s Hs eps Heps.
  unfold is_inf in Hs.
  destruct Hs as [Hlo Hgeatest].
  assert (H: ~ (forall x, S x -> s + eps <= x)).
  { intro Hcontra.
    apply Hgeatest in Hcontra.
    lra.
  }
  apply not_all_ex_not in H.
  destruct H as [x Hx].
  exists x.
  split.
  - apply not_imply_elim in Hx. exact Hx.
  - apply not_imply_elim2 in Hx. lra.
Qed.

(* ================================================================ *)
(*  主定理                                                            *)
(* ================================================================ *)

Theorem monotone_no_second_kind :
  forall (f : R -> R) (a b : R),
  monotone f a b ->
  no_second_kind_discontinuity f a b.
Proof.
  intros f a b Hmon.
  unfold no_second_kind_discontinuity.
  intros x Hx.
  destruct Hmon as [Hinc|Hdec].
  - (* 单调增情形 *)
    split.
    + (* 左极限存在：sup{f(y) : a < y < x} *)
      assert (Hnondom: exists r, exists y, a < y < x /\ f y = r).
      { exists (f ((a + x) / 2)). exists ((a + x) / 2). split. lra. reflexivity. }
      assert (Hboundom: exists m, forall r, (exists y, a < y < x /\ f y = r) -> r <= m).
      { exists (f x). intros r [y [Hy Hfy]]. rewrite <- Hfy.
        assert (Hyb: a < y < b). lra.
        apply Hinc. exact Hyb. lra. lra.
      }
      destruct (completeness_sup (fun r => exists y, a < y < x /\ f y = r) Hnondom Hboundom) as [s Hs].
      exists s. intros eps Heps.
        assert (Hexists: exists r, (exists y, a < y < x /\ f y = r) /\ s - eps < r).
        { apply (sup_adherent (fun r => exists y, a < y < x /\ f y = r) s Hs eps Heps). }
        destruct Hexists as [r [Hy Hyf]].
        destruct Hy as [y [Hy Hfy]].
        exists (x - y). split. lra.
        intros y0 [Hya0 Hy0x] Hy0delta.
        assert (f y0 <= s). { apply (proj1 Hs). exists y0. split. split. exact Hya0. exact Hy0x. reflexivity. }
        assert (s - eps < f y0).
        { assert (Hlt: y < y0).
          { assert (Hx_y0: x - y0 >= 0). lra.
            assert (Habs: Rabs (x - y0) = x - y0). { apply Rabs_right. apply Rle_ge. lra. }
            rewrite Habs in Hy0delta. lra.
          }
          assert (f y <= f y0). { assert (Hyb: a < y < b). lra. apply Hinc. exact Hyb. split. exact Hya0. lra. lra. }
          lra.
        }
        assert (Hfs: f y0 - s <= 0). lra.
        assert (Habs: Rabs (f y0 - s) = s - f y0).
        { destruct (Rcase_abs (f y0 - s)).
          - rewrite Rabs_left. lra. lra.
          - rewrite Rabs_right. lra. lra.
        }
        rewrite Habs. lra.
    + (* 右极限存在：inf{f(y) : x < y < b} *)
      assert (Hnondom: exists r, exists y, x < y < b /\ f y = r).
      { exists (f ((x + b) / 2)). exists ((x + b) / 2). split. lra. reflexivity. }
      assert (Hboundom: exists m, forall r, (exists y, x < y < b /\ f y = r) -> m <= r).
      { exists (f x). intros r [y [Hy Hfy]]. rewrite <- Hfy.
        assert (Hyb: a < y < b). lra.
        apply Hinc. lra. exact Hyb. lra.
      }
      destruct (completeness_inf (fun r => exists y, x < y < b /\ f y = r) Hnondom Hboundom) as [s Hs].
      exists s. intros eps Heps.
        assert (Hexists: exists r, (exists y, x < y < b /\ f y = r) /\ r < s + eps).
        { apply (inf_adherent (fun r => exists y, x < y < b /\ f y = r) s Hs eps Heps). }
        destruct Hexists as [r [Hy Hyf]].
        destruct Hy as [y [Hy Hfy]].
        exists (y - x). split. lra.
        intros y0 [Hxy0 Hy0b] Hy0delta.
        assert (s <= f y0). { apply (proj1 Hs). exists y0. split. split. exact Hxy0. exact Hy0b. reflexivity. }
        assert (f y0 < s + eps).
        { assert (Hlt: y0 < y).
          { destruct (Rtotal_order y0 y) as [Hlt'|[Heq|Hgt']].
            - exact Hlt'.
            - intros [Heq'|Hgt''].
            - destruct Heq as [Heq'|Hgt''].
              * exfalso. rewrite <- Heq' in Hy0delta.
                assert (Habs: Rabs (x - y) = y - x).
                { assert (Hx_y: x - y < 0). lra.
                  rewrite Rabs_left. lra. lra.
                }
                rewrite Habs in Hy0delta. lra.
              * exfalso. lra.
          }
          assert (Habs: Rabs (x - y0) = y0 - x).
          { assert (Hx_y0_lt: x - y0 < 0). lra.
            rewrite Rabs_left. lra. lra.
          }
          rewrite Habs in Hy0delta. lra.
        }
        assert (f y0 <= f y). { assert (Hyb: a < y0 < b). lra. apply Hinc. lra. exact Hyb. lra. }
        lra.
        assert (Hfs: s - f y0 <= 0). lra.
        assert (Habs: Rabs (f y0 - s) = f y0 - s).
        { destruct (Rcase_abs (f y0 - s)).
          - rewrite Rabs_left. lra. lra.
          - rewrite Rabs_right. lra. lra.
        }
        rewrite Habs. lra.
  - (* 单调减情形：转化为 -f 单调增 *)
    assert (Hmono_inc: monotone_inc (fun x => -f x) a b).
    { unfold monotone_inc. intros x0 y0 Hx0 Hy0 Hlt. specialize (Hdec x0 y0 Hx0 Hy0 Hlt). lra. }
    assert (Hneg: no_second_kind_discontinuity (fun x => -f x) a b).
    { apply monotone_no_second_kind. left. exact Hmono_inc. }
    specialize (Hneg x Hx).
    destruct Hneg as [Hleft Hright].
    split.
    + unfold left_limit_exists. specialize (Hleft).
      intros. destruct Hleft as [l Hl]. exists (-l).
      intros eps Heps. specialize (Hl eps Heps).
      destruct Hl as [delta [Hdelta Hl]].
      exists delta. split. exact Hdelta.
      intros y Hy Hdelta'. specialize (Hl y Hy Hdelta').
      lra.
    + unfold right_limit_exists. specialize (Hright).
      intros. destruct Hright as [l Hl]. exists (-l).
      intros eps Heps. specialize (Hl eps Heps).
      destruct Hl as [delta [Hdelta Hl]].
      exists delta. split. exact Hdelta.
      intros y Hy Hdelta'. specialize (Hl y Hy Hdelta').
      lra.
Qed.

Close Scope R_scope.
