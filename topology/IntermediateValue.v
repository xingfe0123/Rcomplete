(*
  ================================================================================
  IntermediateValue.v — 介值定理（Intermediate Value Theorem）
  ================================================================================

  作者: luoxing
  日期: 2026-08-09
  Rocq 版本: 9.1.1 (Stdlib)

  定理：f: [a,b] → R 连续，f(a) < c < f(b) ⟹ ∃ x ∈ (a,b), f(x) = c
  ================================================================================
*)

From Stdlib Require Import Reals Lra ClassicalEpsilon ArithRing.

Open Scope R_scope.

(* ================================================================ *)
(*  定义                                                              *)
(* ================================================================ *)

Definition continuous_at (f : R -> R) (x0 : R) : Prop :=
  forall eps, eps > 0 ->
    exists delta, delta > 0 /\
      forall x, Rabs (x - x0) < delta -> Rabs (f x - f x0) < eps.

Definition continuous_on_interval (f : R -> R) (a b : R) : Prop :=
  forall x, a <= x <= b -> continuous_at f x.

Definition is_sup (S : R -> Prop) (m : R) : Prop :=
  (forall x, S x -> x <= m) /\
  (forall m', (forall x, S x -> x <= m') -> m <= m').

Definition bounded_nonempty (S : R -> Prop) : Prop :=
  (exists x, S x) /\ (exists m, forall x, S x -> x <= m).

Axiom completeness : forall S : R -> Prop,
  bounded_nonempty S -> { m : R | is_sup S m }.

(* ================================================================ *)
(*  引理                                                              *)
(* ================================================================ *)

Lemma continuous_pos :
  forall (f : R -> R) (x0 : R),
  continuous_at f x0 -> f x0 > 0 ->
  exists delta, delta > 0 /\
    forall x, Rabs (x - x0) < delta -> f x > 0.
Proof.
  intros f x0 Hcont Hpos.
  assert (Hand: f x0 / 2 > 0).
  { assert (inv2_gt_0: /2 > 0). { apply Rinv_0_lt_compat. lra. }
    assert (f x0 * /2 > 0). { apply Rmult_gt_0_compat. lra. lra. }
    unfold Rdiv. lra.
  }
  destruct (Hcont (f x0 / 2)) as [delta [Hdelta Hf]].
  - exact Hand.
  - exists delta. split. exact Hdelta.
    intros x Hx.
    specialize (Hf x Hx).
    assert (Habs: Rabs (f x - f x0) < f x0 / 2). lra.
    unfold Rminus in Habs.
    apply Rabs_def2 in Habs.
    lra.
Qed.

Lemma continuous_neg :
  forall (f : R -> R) (x0 : R),
  continuous_at f x0 -> f x0 < 0 ->
  exists delta, delta > 0 /\
    forall x, Rabs (x - x0) < delta -> f x < 0.
Proof.
  intros f x0 Hcont Hneg.
  assert (Hand: - f x0 / 2 > 0).
  { assert (inv2_gt_0: /2 > 0). { apply Rinv_0_lt_compat. lra. }
    assert (- f x0 * /2 > 0). { apply Rmult_gt_0_compat. lra. lra. }
    unfold Rdiv. lra.
  }
  destruct (Hcont (- f x0 / 2)) as [delta [Hdelta Hf]].
  - exact Hand.
  - exists delta. split. exact Hdelta.
    intros x Hx.
    specialize (Hf x Hx).
    assert (Habs: Rabs (f x - f x0) < - f x0 / 2). lra.
    unfold Rminus in Habs.
    apply Rabs_def2 in Habs.
    lra.
Qed.

(* ================================================================ *)
(*  主定理                                                            *)
(* ================================================================ *)

Theorem intermediate_value_theorem :
  forall (f : R -> R) (a b c : R),
  a < b ->
  continuous_on_interval f a b ->
  f a < c < f b ->
  exists x, a < x < b /\ f x = c.
Proof.
  intros f a b c Hab Hcont Hc.
  assert (Hex: exists x, a <= x <= b /\ f x < c).
  { exists a. split. lra. lra. }
  assert (Hbound: exists m, forall x, (a <= x <= b /\ f x < c) -> x <= m).
  { exists b. intros x [Hx _]. lra. }
  destruct (completeness (fun x => a <= x <= b /\ f x < c)) as [xi [Hsup Hleast]].
  - split. exact Hex. exact Hbound.
  - assert (Hxi_ab : a <= xi <= b).
    { split.
      - assert (H: a <= a <= b /\ f a < c). { split. lra. lra. }
        specialize (Hsup a H). lra.
      - assert (H: forall x, a <= x <= b /\ f x < c -> x <= b).
        { intros x [Hx _]. lra. }
        specialize (Hleast b H). lra.
    }
    assert (Hfic: f xi = c).
    { destruct (Rtotal_order (f xi) c) as [Hlt|[Heq|Hgt]].
      - set (g := fun x => f x - c).
        assert (Hcont_g: continuous_at g xi).
        { unfold continuous_at. intros eps Heps.
          destruct (Hcont xi Hxi_ab eps Heps) as [delta [Hdelta Hf]].
          exists delta. split. exact Hdelta.
          intros x Hx. specialize (Hf x Hx).
          unfold g.
          replace (f x - c - (f xi - c)) with (f x - f xi).
          2: { lra. }
          lra.
        }
        assert (Hg_neg: g xi < 0). { unfold g. lra. }
        destruct (continuous_neg _ _ Hcont_g Hg_neg) as [delta [Hdelta Hf]].
        assert (Hexists: exists x, a <= x <= b /\ f x < c /\ xi < x).
          { assert (Hxi_lt_b: xi < b).
            { assert (H: xi <= b). lra.
              destruct (Rtotal_order xi b) as [Hlt'|[Heq|Hgt]].
              - exact Hlt'.
              - exfalso. rewrite <- Heq in Hlt. assert (Hbc: f b > c). lra. lra.
              - exfalso. lra.
            }
            assert (Hmin: Rmin (delta / 2) (b - xi) > 0).
            { apply Rmin_case.
              - assert (delta / 2 > 0). lra. lra.
              - lra.
            }
            exists (xi + Rmin (delta / 2) (b - xi)).
            split.
            - split. lra. lra.
            - split.
              + apply Hf.
                assert (Rabs (xi + Rmin (delta / 2) (b - xi) - xi) = Rmin (delta / 2) (b - xi)).
                { unfold Rminus. rewrite Rplus_comm. rewrite Rplus_minus.
                  apply Rabs_right. apply Rle_ge. lra. }
                rewrite H. lra.
              + lra.
          }
          destruct Hexists as [x [Hx [Hfx Hxi_lt]]].
          specialize (Hsup x (conj Hx Hfx)).
          lra.
      - exact Heq.
      - set (g := fun x => f x - c).
        assert (Hcont_g: continuous_at g xi).
        { unfold continuous_at. intros eps Heps.
          destruct (Hcont xi Hxi_ab eps Heps) as [delta [Hdelta Hf]].
          exists delta. split. exact Hdelta.
          intros x Hx. specialize (Hf x Hx).
          unfold g.
          replace (f x - c - (f xi - c)) with (f x - f xi).
          2: { lra. }
          lra.
        }
        assert (Hg_pos: g xi > 0). { unfold g. lra. }
        destruct (continuous_pos _ _ Hcont_g Hg_pos) as [delta [Hdelta Hf]].
        assert (Hle: forall x, a <= x <= b /\ f x < c -> x <= xi - Rmin (delta / 2) (xi - a)).
          { intros x [Hx Hfx].
            assert (Hxi_gt_a: xi > a).
            { assert (H: a <= xi). lra.
              destruct (Rtotal_order xi a) as [Hlt'|[Heq|Hgt']].
              - exfalso. lra.
              - exfalso. rewrite <- Heq in Hgt. lra.
              - exact Hgt'.
            }
            apply Rnot_lt_le. intro Hlt.
            assert (Hclose: Rabs (x - xi) < delta).
            { assert (xi - Rmin (delta / 2) (xi - a) < x). lra.
              assert (x - xi < Rmin (delta / 2) (xi - a)). lra.
              assert (Rabs (x - xi) = xi - x).
              { apply Rabs_left. lra. }
              rewrite H. lra.
            }
            specialize (Hf x Hclose).
            lra.
          }
          apply Hleast in Hle.
          assert (xi - Rmin (delta / 2) (xi - a) < xi). lra.
          lra.
    }
    exists xi.
    split.
    + split.
      - assert (xi > a).
        { apply Rle_lt_trans with a.
          - assert (H: a <= a <= b /\ f a < c). { split. lra. lra. }
            specialize (Hsup a H). lra.
          - lra. }
        lra.
      - assert (xi < b).
        { apply Rlt_le_trans with b.
          - lra.
          - assert (H: forall x, a <= x <= b /\ f x < c -> x <= b).
            { intros x [Hx _]. lra. }
            specialize (Hleast b H). lra.
        }
        lra.
    + exact Hfic.
Qed.

Close Scope R_scope.
