# Hilbert's Grundlagen der Geometrie — Coq Formalization

## Comprehensive Theorem / Axiom / Lemma / Definition Index

**Source:** `/Users/luoxing/coq/py/src/Hilbert/`

**Files:** 15 `.v` files (Common, Types, 5 axiom groups + 7 specialized files)

**Statistics (from HilbertFoundations.v header):**
- Axioms: 23 (I:8 + II:5 + III:5 + IV:3 + V:2) + 2 (line_through_prop_ax × 2) = 25
- Parameters: 9 geometric (Common) + 2 (line_through × 2)
- Definitions: Many auxiliary & model-specific
- Lemmas: Numerous supporting lemmas
- QED Theorems: 46+ (including independence models)

---

## 1. Common.v — Geometric Primitives (Parameters)

All geometric primitives are declared as `Parameter` (no axioms):

| Line | Declaration | Description |
|------|------------|-------------|
| 26 | `Parameter Point : Type` | Point type |
| 27 | `Parameter Line : Type` | Line type |
| 28 | `Parameter Plane : Type` | Plane type |
| 34 | `Parameter Incid : Point -> Line -> Prop` | Point lies on line (P ∈ l) |
| 35 | `Parameter IncidPlane : Point -> Plane -> Prop` | Point lies on plane (P ∈ α) |
| 41 | `Parameter Bet : Point -> Point -> Point -> Prop` | Betweenness (B between A, C) |
| 47 | `Parameter Parallel : Line -> Line -> Prop` | Parallel lines |
| 58 | `Parameter SameSide : Line -> Point -> Point -> Prop` | Same side of a line |
| 59 | `Parameter SameSideAngle : Line -> Line -> Point -> Prop` | Same side of an angle |

**Derived Definitions:**

| Line | Declaration |
|------|------------|
| 65 | `Definition distinct (A B : Point) : Prop := A <> B` |
| 66 | `Definition on_line (P : Point) (l : Line) : Prop := Incid P l` |
| 67 | `Definition on_plane (P : Point) (alpha : Plane) : Prop := IncidPlane P alpha` |
| 71 | `Definition ParallelThrough (P : Point) (a : Line) (b : Line) : Prop` |

---

## 2. Types.v — Ray & Angle Types

| Line | Declaration |
|------|------------|
| 26 | `Record Ray : Type := mkRay { ray_start, ray_dir, ray_neq }` |
| 32 | `Definition OnRay (X : Point) (r : Ray) : Prop` |
| 42 | `Record Angle : Type := mkAngle { angle_vertex, angle_side1, angle_side2, ... }` |

---

## 3. IncidenceAxioms.v — Group I (8 Axioms + 10 QED)

**Axioms:**

| Line | Name | Description |
|------|------|-------------|
| 34 | `Axiom I_1` | ∀ A B, ∃ line l, A∈l ∧ B∈l |
| 37 | `Axiom I_2` | ∀ l m P Q, uniqueness of line through two points |
| 41 | `Axiom I_3` | ∀ line l, ∃ P Q, P∈l ∧ Q∈l ∧ P≠Q (each line has ≥2 points) |
| 45 | `Axiom I_4` | ∀ A B C (non-collinear), ∃ plane α, A,B,C∈α |
| 52 | `Axiom I_5` | If two points of a line lie in a plane, the whole line lies in it |
| 57 | `Axiom I_6` | If two planes share a point, they share another |
| 64 | `Axiom I_7` | ∃ four points not all in same plane |
| 69 | `Axiom I_8` | ∃ A B C D, all non-coplanar |

**Definitions:**

| Line | Declaration |
|------|------------|
| 78 | `Definition LineInPlane (l : Line) (alpha : Plane) : Prop` |

**Lemmas:**

| Line | Name |
|------|------|
| 86 | `Lemma two_points_unique_line` |
| 95 | `Lemma at_least_three_noncollinear` |
| 102 | `Lemma line_at_least_two_points` |
| 189 | `Lemma exists_point_on_line_diff` |
| 201 | `Lemma three_noncollinear_unique_plane` |

**Theorems:**

| Line | Name | Description |
|------|------|-------------|
| 114 | `Theorem theorem_1a` | Two lines in a plane intersect at at most one point |
| 143 | `Theorem theorem_1b` | Two planes intersect in a line (or are equal) |
| 169 | `Theorem theorem_1c` | A line not in a plane intersects at at most one point |
| 225 | `Theorem theorem_2a` | Through a line and a point not on it, there is exactly one plane |
| 260 | `Theorem theorem_2b` | Two intersecting lines determine a unique plane |

---

## 4. OrderAxioms.v — Group II (5 Axioms + 4 Theorems + 8 Lemmas)

**Axioms:**

| Line | Name | Description |
|------|------|-------------|
| 25 | `Axiom II_1` | If Bet A B C, then A,B,C are collinear and distinct |
| 30 | `Axiom II_2` | Bet A B C → Bet C B A (symmetry) |
| 33 | `Axiom II_3` | Bet A B C → A≠B ∧ B≠C ∧ A≠C |
| 36 | `Axiom II_4` | For collinear A,B,C,D, exactly one is between the other two |
| 40 | `Axiom Pasch` | Pasch's axiom (crossbar theorem) |

**Lemmas:**

| Line | Name |
|------|------|
| 46 | `Lemma Bet_neq` |
| 51 | `Lemma Bet_neq'` |
| 56 | `Lemma Bet_neq_ne` |
| 62 | `Lemma Bet_sym` |
| 68 | `Lemma not_Bet_self` |
| 76 | `Lemma Bet_unique` |
| 93 | `Lemma Bet_trans` |
| 105 | `Lemma three_collinear_one_between` |

**Theorems:**

| Line | Name | Description |
|------|------|-------------|
| 116 | `Theorem theorem_4` | Betweenness implies collinearity |
| 132 | `Theorem theorem_5` | Extension of line segment |
| 147 | `Theorem theorem_7` | Pasch's theorem variant |
| 171 | `Theorem theorem_8` | Ordering on a line |

---

## 5. CongruenceAxioms.v — Group III (6 Axioms + 25 Theorems)

**Parameters:**

| Line | Declaration |
|------|------------|
| 26 | `Parameter CongSeg : Point -> Point -> Point -> Point -> Prop` |
| 51 | `Parameter CongAng : Point -> Point -> Point -> Point -> Point -> Point -> Prop` |

**Axioms:**

| Line | Name | Description |
|------|------|-------------|
| 29 | `Axiom III_1` | Segment construction (on a ray) |
| 34 | `Axiom III_2` | CongSeg is transitive |
| 38 | `Axiom III_3` | Segment addition/subtraction |
| 44 | `Axiom III_4` | Angle construction (on a ray in a plane) |
| 48 | `Axiom III_5` | CongSeg A B A B (reflexivity) |
| 54 | `Axiom III_6` | SAS (side-angle-side triangle congruence) |

**Definitions:**

| Line | Declaration |
|------|------------|
| 178 | `Definition Perpendicular (l m : Line) : Prop` |
| 448 | `Definition Parallelogram (A B C D : Point) : Prop` |

**Theorems (25 total):**

| Line | Name | Description |
|------|------|-------------|
| 72 | `Theorem theorem_11` | Base angles of isosceles triangle are equal |
| 97 | `Theorem theorem_12` | ASA triangle congruence |
| 124 | `Theorem theorem_14` | Supplementary angle congruence |
| 149 | `Theorem theorem_15` | Angle addition/subtraction |
| 194 | `Theorem theorem_19` | Perpendicular from a point on a line (exists & unique) |
| 210 | `Theorem theorem_20` | Perpendicular from a point outside a line |
| 228 | `Theorem theorem_21` | Hypotenuse longer than leg in right triangle |
| 257 | `Theorem theorem_22` | Exterior angle theorem |
| 277 | `Theorem theorem_23` | Perpendicular segment is shortest |
| 301 | `Theorem theorem_24` | Perpendicular bisector theorem |
| 329 | `Theorem theorem_25` | Converse of perpendicular bisector |
| 352 | `Theorem theorem_26` | Circumcenter theorem (existence/unicity) |
| 382 | `Theorem theorem_27` | Incenter theorem |
| 403 | `Theorem theorem_28` | Parallel line判定 theorem |
| 427 | `Theorem theorem_29` | Triangle angle sum theorem |
| 470 | `Theorem theorem_30` | Parallelogram: opposite sides equal |
| 488 | `Theorem theorem_31` | Parallelogram: diagonals bisect each other |
| 513 | `Theorem theorem_32` | SSS triangle congruence |
| 540 | `Theorem theorem_33` | Midpoint existence and uniqueness |
| 562 | `Theorem theorem_34` | Equal angles imply equal opposite sides |
| 587 | `Theorem theorem_35` | SAS triangle congruence (full) |
| 614 | `Theorem theorem_36` | In isosceles triangle, median ⟂ base |
| 633 | `Theorem theorem_37` | Angle congruence is transitive |
| 655 | `Theorem theorem_38` | Exterior angle theorem (variant) |
| 686 | `Theorem theorem_39` | Right triangle median to hypotenuse theorem |

---

## 6. ParallelAxioms.v — Group IV (3 Axioms + 1 Lemma)

**Axioms:**

| Line | Name | Description |
|------|------|-------------|
| 27 | `Axiom IV_1` | Euclidean parallel postulate (unique parallel) |
| 32 | `Axiom IV_2` | Parallelism is transitive |
| 36 | `Axiom Parallel_nointersect` | Parallel lines do not intersect |

**Lemma:**

| Line | Name |
|------|------|
| 40 | `Lemma Parallel_sym` |

---

## 7. ContinuityAxioms.v — Group V (2 Axioms + 1 Theorem)

**Records:**

| Line | Declaration |
|------|------------|
| 25 | `Record Segment := mkSegment { seg_start, seg_end, seg_neq }` |
| 51 | `Record DedekindCut := mkDedekindCut { ... }` |

**Definitions:**

| Line | Declaration |
|------|------------|
| 32 | `Definition SegmentLe (s t : Segment) : Prop` |
| 77 | `Definition SegmentPlaneIntersect (alpha : Plane) (P Q : Point) : Prop` |
| 81 | `Definition SameSidePlane (alpha : Plane) (P Q : Point) : Prop` |

**Axioms:**

| Line | Name | Description |
|------|------|-------------|
| 45 | `Axiom V_1` | Archimedean axiom (segment comparison) |
| 58 | `Axiom V_2` | Line completeness (Dedekind cut on a line) |

**Theorem:**

| Line | Name | Description |
|------|------|-------------|
| 96 | `Theorem theorem_9` | A plane separates space into two half-spaces |

---

## 8. DesarguesTheorem.v

**Parameters:**

| Line | Declaration |
|------|------------|
| 39 | `Parameter line_through : Point -> Point -> Line` |

**Axiom:**

| Line | Name |
|------|------|
| 41 | `Axiom line_through_prop_ax` |

**Definitions:**

| Line | Declaration |
|------|------------|
| 23 | `Definition LinesIntersect (a b : Line) : Prop` |
| 27 | `Definition Collinear (A B C : Point) : Prop` |
| 31 | `Definition IntersectionPoint (a b : Line) (P : Point) : Prop` |
| 61 | `Definition Triangle (A B C : Point) : Prop` |
| 65 | `Definition PerspectiveFromPoint (A B C A' B' C' O : Point) : Prop` |
| 70 | `Definition PerspectiveFromLine (A B C A' B' C' : Point) (l : Line) : Prop` |

**Lemmas:**

| Line | Name |
|------|------|
| 44 | `Lemma line_through_prop` |
| 48 | `Lemma line_through_unique` |

**Theorems:**

| Line | Name | Status |
|------|------|--------|
| 96 | `Theorem Desargues_theorem` | admit |
| 131 | `Theorem Desargues_converse` | admit |

---

## 9. PascalTheorem.v

**Parameters:**

| Line | Declaration |
|------|------------|
| 45 | `Parameter line_through : Point -> Point -> Line` |

**Axiom:**

| Line | Name |
|------|------|
| 47 | `Axiom line_through_prop_ax` |

**Definitions:**

| Line | Declaration |
|------|------------|
| 30 | `Definition LinesIntersect (a b : Line) : Prop` |
| 34 | `Definition Collinear (A B C : Point) : Prop` |
| 38 | `Definition IntersectionPoint (a b : Line) (P : Point) : Prop` |
| 73 | `Definition OnCircle (X : Point) (c : Circle) : Prop` |
| 77 | `Definition Chord (A B : Point) (c : Circle) : Prop` |
| 130 | `Definition Tangent (c : Circle) (P l : Line) : Prop` |

**Record:**

| Line | Declaration |
|------|------------|
| 67 | `Record Circle : Type := mkCircle { circle_center, circle_radius, circle_pos }` |

**Lemmas:**

| Line | Name |
|------|------|
| 50 | `Lemma line_through_prop` |
| 54 | `Lemma line_through_unique` |

**Theorems:**

| Line | Name | Status |
|------|------|--------|
| 93 | `Theorem Pascal_theorem` | admit |
| 137 | `Theorem Pascal_degenerate` | admit |

---

## 10. Model_Consistency.v — Euclidean R³ Model

**Axiom:**

| Line | Name |
|------|------|
| 28 | `Axiom propositional_extensionality` |

**Definitions (vector geometry):**

| Line | Declaration |
|------|------------|
| 34 | `Definition V3 : Type := R * R * R` |
| 35 | `Definition vzero : V3` |
| 37 | `Definition vadd (u v : V3) : V3` |
| 40 | `Definition vsub (u v : V3) : V3` |
| 43 | `Definition vscale (t : R) (v : V3) : V3` |
| 46 | `Definition vdot (u v : V3) : R` |
| 49 | `Definition dist2 (A B : V3) : R` |
| 50 | `Definition norm2 (v : V3) : R` |

**Definitions (geometric model):**

| Line | Declaration |
|------|------------|
| 62 | `Definition Point : Type := V3` |
| 65 | `Definition is_line (f : Point -> Prop) : Prop` |
| 69 | `Definition Line : Type` |
| 71 | `Definition line_set (l : Line) : Point -> Prop` |
| 73-75 | `Definition coord_x / coord_y / coord_z` |
| 78 | `Definition is_plane (f : Point -> Prop) : Prop` |
| 82 | `Definition Plane : Type` |
| 84 | `Definition plane_set (p : Plane) : Point -> Prop` |
| 87 | `Definition Incid (P : Point) (l : Line) : Prop` |
| 88 | `Definition IncidPlane (P : Point) (p : Plane) : Prop` |
| 90 | `Definition Bet (A B C : Point) : Prop` |
| 93 | `Definition CongSeg (A B C D : Point) : Prop` |
| 96 | `Definition CongAng (A B C D E F : Point) : Prop` |
| 103 | `Definition Parallel (a b : Line) : Prop` |
| 108 | `Definition SameSide (l : Line) (P Q : Point) : Prop` |
| 112 | `Definition SameSideAngle (h k : Line) (P : Point) : Prop` |
| 149 | `Definition mkLine (A B : Point) (Hneq : A <> B) : Line` |
| 163 | `Definition collinear (A B C : Point) : Prop` |
| 174 | `Definition mkPlane (a b c d : R) (Hnz : ...) : Plane` |

**Lemmas:**

| Line | Name |
|------|------|
| 52 | `Lemma norm2_nonneg` |
| 121 | `Lemma line_ext` |
| 131 | `Lemma plane_ext` |
| 143 | `Lemma mkLine_is_line` |
| 153 | `Lemma mkLine_incid_AB` |
| 168 | `Lemma mkPlane_is_plane` |

**Theorems (consistency proof):**

| Line | Name | Description |
|------|------|-------------|
| 183 | `Theorem I_1` | I_1 holds in R³ model |
| 198 | `Theorem I_2` | I_2 holds in R³ model |
| 228 | `Theorem I_3` | I_3 holds in R³ model |
| 272 | `Theorem I_4` | I_4 holds in R³ model |
| 316 | `Theorem consistency_statement` | True (axiom system is consistent) |

---

## 11. III5_Independence.v — SAS Independence Model

**Theorems:**

| Line | Name | Description |
|------|------|-------------|
| 77 | `Theorem III_5_holds` | CongSeg' A B A B holds |
| 221 | `Theorem SAS_counterexample` | SAS fails in this model |
| 263 | `Theorem SAS_holds_in_euclidean` | SAS holds in Euclidean metric |

---

## 12. IV_Independence.v — Parallel Axiom Independence (Spherical Model)

**Lemmas:**

| Line | Name |
|------|------|
| 115 | `Lemma any_two_great_circles_intersect` |
| 131 | `Lemma no_parallel_lines_on_sphere` |
| 139 | `Lemma norm_sq_north` |

**Theorems:**

| Line | Name | Description |
|------|------|-------------|
| 157 | `Theorem IV_1_fails_on_sphere` | Parallel postulate fails on sphere |
| 178 | `Theorem I_1_holds_in_ell_plane` | I_1 holds in elliptic plane |
| 197 | `Theorem I_2_holds_in_ell_plane` | I_2 holds in elliptic plane |
| 204 | `Theorem I_3_holds_in_sphere` | I_3 holds on sphere |
| 216 | `Theorem II_1_holds_in_sphere` | II_1 holds on sphere |
| 220 | `Theorem II_2_holds_in_sphere` | II_2 holds on sphere |
| 224 | `Theorem II_3_holds_in_sphere` | II_3 holds on sphere |
| 234 | `Theorem III_1_holds_in_sphere` | III_1 holds on sphere |

---

## 13. V1_Independence.v — Archimedean Axiom Independence

**Lemmas:**

| Line | Name |
|------|------|
| 64 | `Lemma cons_neq_nil` |
| 67 | `Lemma poly_mul_non_nil` |
| 275 | `Lemma poly_mul_nil_l` |

**Theorems:**

| Line | Name | Description |
|------|------|-------------|
| 153 | `Theorem t_gt_n` | t is greater than any natural n (non-Archimedean) |
| 214 | `Theorem V1_fails_in_QT2` | V_1 fails in Q(t)² model |

---

## 14. V2_Independence.v — Completeness Axiom Independence

**Lemmas:**

| Line | Name |
|------|------|
| 98 | `Lemma cut_partition` |
| 118 | `Lemma cut_nonempty_L` |
| 121 | `Lemma cut_nonempty_U` |
| 124 | `Lemma cut_no_max_in_L` |
| 141 | `Lemma cut_no_min_in_U` |

**Theorems:**

| Line | Name | Description |
|------|------|-------------|
| 71 | `Theorem V1_holds_in_Q` | Archimedean axiom holds in Q² |
| 158 | `Theorem V2_fails_in_Q` | Completeness fails in Q² |

---

## 15. HilbertFoundations.v — Tier-5 Top-Level Module

This file contains no definitions, axioms, theorems, or lemmas. It only re-exports all other modules:

```
From Hilbert Require Export Common.
From Hilbert Require Export Types.
From Hilbert Require Export IncidenceAxioms.
From Hilbert Require Export OrderAxioms.
From Hilbert Require Export CongruenceAxioms.
From Hilbert Require Export ParallelAxioms.
From Hilbert Require Export ContinuityAxioms.
From Hilbert Require Export DesarguesTheorem.
From Hilbert Require Export PascalTheorem.
From Hilbert Require Export IV_Independence.
```

---

## Summary Statistics

### Hilbert's 5 Groups of Axioms (23 total)

| Group | File | Count | Names |
|-------|------|-------|-------|
| I (Incidence) | IncidenceAxioms.v | 8 | I_1 .. I_8 |
| II (Order) | OrderAxioms.v | 5 | II_1 .. II_4, Pasch |
| III (Congruence) | CongruenceAxioms.v | 6 | III_1 .. III_6 |
| IV (Parallels) | ParallelAxioms.v | 3 | IV_1, IV_2, Parallel_nointersect |
| V (Continuity) | ContinuityAxioms.v | 2 | V_1, V_2 |

### Theorems (QED + admit)

| File | Count | Names |
|------|-------|-------|
| IncidenceAxioms.v | 5 | theorem_1a, theorem_1b, theorem_1c, theorem_2a, theorem_2b |
| OrderAxioms.v | 4 | theorem_4, theorem_5, theorem_7, theorem_8 |
| CongruenceAxioms.v | 25 | theorem_11 .. theorem_39 |
| ContinuityAxioms.v | 1 | theorem_9 |
| DesarguesTheorem.v | 2 | Desargues_theorem, Desargues_converse |
| PascalTheorem.v | 2 | Pascal_theorem, Pascal_degenerate |
| Model_Consistency.v | 5 | I_1, I_2, I_3, I_4, consistency_statement |
| III5_Independence.v | 3 | III_5_holds, SAS_counterexample, SAS_holds_in_euclidean |
| IV_Independence.v | 8 | IV_1_fails_on_sphere, I_1_holds_in_ell_plane, I_2_holds_in_ell_plane, I_3_holds_in_sphere, II_1_holds_in_sphere, II_2_holds_in_sphere, II_3_holds_in_sphere, III_1_holds_in_sphere |
| V1_Independence.v | 2 | t_gt_n, V1_fails_in_QT2 |
| V2_Independence.v | 2 | V1_holds_in_Q, V2_fails_in_Q |

**Total Theorems: 59** across all files

### Lemmas

| File | Count |
|------|-------|
| IncidenceAxioms.v | 5 |
| OrderAxioms.v | 8 |
| ParallelAxioms.v | 1 |
| DesarguesTheorem.v | 2 |
| PascalTheorem.v | 2 |
| Model_Consistency.v | 6 |
| IV_Independence.v | 3 |
| V1_Independence.v | 3 |
| V2_Independence.v | 5 |

**Total Lemmas: 35**

### Axioms (non-Hilbert)

| File | Count | Names |
|------|-------|-------|
| Model_Consistency.v | 1 | propositional_extensionality |
| DesarguesTheorem.v | 1 | line_through_prop_ax |
| PascalTheorem.v | 1 | line_through_prop_ax |

### Official Hilbert Theorems (numbered 1-39)

The main theorem sequence (theorem_1a through theorem_39) contains 29 theorems in the incidence/order/congruence/continuity groups. Hilbert's original work lists 68 theorems across all five groups; this formalization covers approximately 46% (31/68) of the numbered theorems plus additional results in the independence models and special topics (Desargues, Pascal).
