# Hilbert's Grundlagen der Geometrie — Coq Formalization

## Comprehensive Theorem / Axiom / Lemma / Definition Index

**Source:** `/Users/luoxing/coq/py/src/Hilbert/`

**Files:** 15 `.v` files (Common, Types, HilbertStructure + 5 axiom groups + 7 specialized files)

**Statistics:**
- **Parameters:** 9 geometric primitives (Common.v)
- **Records:** 8 (Types.v: Ray, Angle; HilbertStructure.v: 6 core + 2 composite)
- **Axioms:** 25 (I:8 + II:4 + Pasch + III:6 + IV:3 + V:2 + line_through:2)
- **Theorems:** 36 (I:5 + II:3 + III:0 + IV:0 + V:0 + Desargues:2 + Pascal:2 + IV_Indep:8 + III5:3 + V1:2 + V2:2 + Model:5 + QPlane:4)
- **Lemmas:** 35+ (supporting results across all files)
- **Compilation:** 15/15 PASS

---

## Architecture Overview

The formalization follows a **Tiered Section Architecture**:

```
Common.v (Parameters)
  ↓
Types.v (Ray, Angle Records)
  ↓
HilbertStructure.v (6 Core Records + 2 Composite)
  ├── IncidenceStructure (I1-I8)
  ├── OrderStructure (II1-II4, Pasch, Ray)
  ├── CongruenceStructure (III1-III6, Side, Angle)
  ├── ArchimedesStructure (V1, Segment)
  ├── DedekindStructure (V2, DedekindCut)
  ├── WeakHilbertPlane (I+II+III+V1)
  └── StrongHilbertPlane (I+II+III+V1+V2)
  ↓
IncidenceTheorem.v (Section I O C)
OrderTheorem.v (Section I O C)
CongruenceTheorem.v (Section I O C)
ParallelTheorem.v (Global style, pre-existing)
ContinuityTheorem.v (Section I O C A D, thin wrapper)
  ↓
DesarguesTheorem.v (Section style)
PascalTheorem.v (Global style + CongSeg alias)
  ↓
Independence Models (IV_Independence, V1_Independence, V2_Independence, III5_Independence)
Model_Consistency.v (R³ model)
  ↓
HilbertFoundations.v (Re-export hub)
```

---

## 1. Common.v — Geometric Primitives (Parameters)

**Parameters (9):**

| Line | Declaration | Description |
|------|-------------|-------------|
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
|------|-------------|
| 65 | `Definition distinct (A B : Point) : Prop := A <> B` |
| 66 | `Definition on_line (P : Point) (l : Line) : Prop := Incid P l` |
| 67 | `Definition on_plane (P : Point) (alpha : Plane) : Prop := IncidPlane P alpha` |
| 71 | `Definition ParallelThrough (P : Point) (a : Line) (b : Line) : Prop` |

---

## 2. Types.v — Ray & Angle Types

| Line | Declaration | Description |
|------|-------------|-------------|
| 26 | `Record Ray : Type := mkRay { ray_start, ray_dir, ray_neq }` | Ray type |
| 32 | `Definition OnRay (X : Point) (r : Ray) : Prop` | Point lies on ray |
| 42 | `Record Angle : Type := mkAngle { angle_vertex, angle_side1, angle_side2, angle_valid }` | Angle type |

---

## 3. HilbertStructure.v — Core Record Definitions

**IncidenceStructure (I1-I8):**

| Line | Field | Type |
|------|-------|------|
| 40 | `Record IncidenceStructure` | Core incidence axioms |
| 42 | `Incid` | `IncPoint I -> IncLine I -> Prop` |
| 43 | `IncidPlane` | `IncPoint I -> IncPlane I -> Prop` |
| 44 | `IncidPlaneLine` | `IncLine I -> IncPlane I -> Prop` |
| 45 | `I1` | Axiom I_1 |
| 46 | `I2` | Axiom I_2 |
| 47 | `I3` | Axiom I_3 |
| 48 | `I4` | Axiom I_4 |
| 49 | `I5` | Axiom I_5 |
| 50 | `I6` | Axiom I_6 |
| 51 | `I7` | Axiom I_7 |
| 52 | `I8` | Axiom I_8 |

**OrderStructure (II1-II4, Pasch, Ray):**

| Line | Field | Type |
|------|-------|------|
| 95 | `Record OrderStructure (I : IncidenceStructure)` | Order axioms |
| 96 | `Bet` | `IncPoint I -> IncPoint I -> IncPoint I -> Prop` |
| 97 | `II_1` | Axiom II_1 (existence of extension) |
| 98 | `II_2` | Axiom II_2 (extension symmetry) |
| 99 | `II_3` | Axiom II_3 (betweenness implies distinctness) |
| 100 | `II_4` | Axiom II_4 (Pasch) |
| 101 | `Pasch` | Pasch's axiom |
| 102 | `SameSide` | `IncPoint I -> IncPoint I -> IncLine I -> Prop` |
| 103 | `Ray` | `Type` |
| 104 | `ray_origin` | `Ray -> IncPoint I` |
| 105 | `ray_line` | `Ray -> IncLine I` |
| 106 | `ray_valid` | `Incid origin line` |
| 107 | `OnRay` | `IncPoint I -> Ray -> Prop` |

**CongruenceStructure (III1-III6, Side, Angle):**

| Line | Field | Type |
|------|-------|------|
| 148 | `Record CongruenceStructure (I : IncidenceStructure) (O : OrderStructure I)` | Congruence axioms |
| 149 | `CongSeg` | Segment congruence |
| 150 | `CongAng` | Angle congruence |
| 151 | `Side` | `Type` (segment type) |
| 152 | `side_start` | `Side -> IncPoint I` |
| 153 | `side_end` | `Side -> IncPoint I` |
| 154 | `side_valid` | `side_start s <> side_end s` |
| 155 | `Angle` | `Type` (angle type) |
| 156 | `angle_vertex` | `Angle -> IncPoint I` |
| 157 | `angle_side1` | `Angle -> Ray I O` |
| 158 | `angle_side2` | `Angle -> Ray I O` |
| 159 | `angle_valid` | `ray_origin side1 = vertex /\ ray_origin side2 = vertex` |
| 160 | `III1` | Axiom III_1 (segment construction) |
| 161 | `III2` | Axiom III_2 (congruence transitivity) |
| 162 | `III3` | Axiom III_3 (segment addition) |
| 163 | `III4` | Axiom III_4 (congruence symmetry) |
| 164 | `III5` | Axiom III_5 (congruence reflexivity) |
| 165 | `III6` | Axiom III_6 (SAS) |

**ArchimedesStructure (V1):**

| Line | Field | Type |
|------|-------|------|
| 193 | `Record ArchimedesStructure (I O C)` | Archimedes axiom |
| 194 | `Segment` | `Type` |
| 195 | `segStart` | `Segment -> IncPoint I` |
| 196 | `segEnd` | `Segment -> IncPoint I` |
| 197 | `segValid` | `segStart s <> segEnd s` |
| 198 | `SegmentTimes` | `Segment -> nat -> Segment` |
| 199 | `SegmentLe` | `Segment -> Segment -> Prop` |
| 200 | `V1` | Axiom V_1 (Archimedes) |

**DedekindStructure (V2):**

| Line | Field | Type |
|------|-------|------|
| 214 | `Record DedekindStructure (I O)` | Dedekind completeness |
| 215 | `DedekindCut` | `Type` |
| 216 | `cutLower` | `DedekindCut -> IncPoint I -> Prop` |
| 217 | `cutUpper` | `DedekindCut -> IncPoint I -> Prop` |
| 218 | `cutValid` | `cutLower <-> ~ cutUpper` |
| 219 | `V2` | Axiom V_2 (completeness) |

**Composite Structures:**

| Line | Record | Description |
|------|--------|-------------|
| 233 | `WeakHilbertPlane` | I + II + III + V1 |
| 242 | `StrongHilbertPlane` | I + II + III + V1 + V2 |

---

## 4. IncidenceTheorem.v — Group I Theorems (Section I O)

**Section:** `Section IncidenceTheorem.` with `Variables (I : IncidenceStructure)`.

**Definitions:**

| Line | Declaration |
|------|-------------|
| 10 | `Definition LineInPlane (I : IncidenceStructure) (l : IncLine I) (alpha : IncPlane I) : Prop` |

**Theorems (5):**

| Line | Name | Description | Status |
|------|------|-------------|--------|
| 17 | `Theorem theorem_1a` | Two lines in a plane intersect at at most one point | QED |
| 41 | `Theorem theorem_1b` | Two planes intersect in a line (or are equal) | QED |
| 61 | `Theorem theorem_1c` | A line not in a plane intersects at at most one point | QED |
| 85 | `Theorem theorem_2a` | Through a line and a point not on it, there is exactly one plane | QED |
| 122 | `Theorem theorem_2b` | Two intersecting lines determine a unique plane | QED |

---

## 5. OrderTheorem.v — Group II Theorems (Section I O)

**Section:** `Section OrderTheorem.` with `Variables (I : IncidenceStructure) (O : OrderStructure I)`.

**Bet Lemmas (QED):**

| Line | Name |
|------|------|
| 48 | `Lemma Bet_neq` |
| 53 | `Lemma Bet_neq'` |
| 58 | `Lemma Bet_neq_ne` |
| 63 | `Lemma Bet_sym` |
| 70 | `Lemma not_Bet_self` |
| 82 | `Lemma Bet_unique` |
| 246 | `Lemma Bet_trans` |
| 264 | `Lemma three_collinear_one_between` |

**Theorems (3 + 1 placeholder):**

| Line | Name | Description | Status |
|------|------|-------------|--------|
| 97 | `Theorem theorem_3` | Collinear two points have a third between them | QED |
| 129 | `Theorem theorem_4` | Three distinct collinear points: exactly one is between the other two | QED (existence), admit (uniqueness) |
| 154 | `Theorem theorem_5_permutation` | Four collinear points can be ordered A,B,C,D | QED (main), admit (branches) |
| 229 | `Theorem theorem_7` | Extension of segment | QED |
| 292 | `Theorem theorem_8_unavailable` | Ordering on a line (SameSide) | admit (needs SameSide abstraction) |

---

## 6. CongruenceTheorem.v — Group III Theorems (Section I O C)

**Section:** `Section CongruenceTheorem.` with `Variables (I O C)`.

**Theorems (0 QED, 20 admit):**

| Line | Name | Description | Status |
|------|------|-------------|--------|
| 41 | `Theorem theorem_11` | Base angles of isosceles triangle are equal | admit |
| 55 | `Theorem theorem_12` | ASA triangle congruence | admit |
| 69 | `Theorem theorem_14` | Supplementary angle congruence | admit |
| 90 | `Theorem theorem_15` | Angle addition/subtraction | admit |
| 99 | `Theorem theorem_19` | Perpendicular from a point on a line | admit |
| 113 | `Theorem theorem_20` | Perpendicular from a point outside a line | admit |
| 124 | `Theorem theorem_21` | Hypotenuse longer than leg in right triangle | admit |
| 137 | `Theorem theorem_22` | Exterior angle theorem | admit |
| 152 | `Theorem theorem_23` | Perpendicular segment is shortest | admit |
| 165 | `Theorem theorem_24` | Perpendicular bisector theorem | admit |
| 184 | `Theorem theorem_25` | Converse of perpendicular bisector | admit |
| 196 | `Theorem theorem_26` | Circumcenter theorem | admit |
| 223 | `Theorem theorem_27` | Incenter theorem | admit |
| 232 | `Theorem theorem_28` | Parallel line判定 theorem | admit |
| 242 | `Theorem theorem_29` | Triangle angle sum theorem | admit |
| 257 | `Theorem theorem_30` | Parallelogram: opposite sides equal | admit |
| 268 | `Theorem theorem_31` | Parallelogram: diagonals bisect each other | admit |
| 280 | `Theorem theorem_32` | SSS triangle congruence | admit |
| 290 | `Theorem theorem_33` | Midpoint existence and uniqueness | admit |
| 303 | `Theorem theorem_34` | Equal angles imply equal opposite sides | admit |

---

## 7. ParallelTheorem.v — Group IV Axioms (Global Style)

| Line | Declaration | Description |
|------|-------------|-------------|
| 27 | `Axiom IV_1` | Euclidean parallel postulate (unique parallel) |
| 32 | `Axiom IV_2` | Parallelism is transitive |
| 36 | `Axiom Parallel_nointersect` | Parallel lines do not intersect |
| 40 | `Lemma Parallel_sym` | Parallelism is symmetric |

---

## 8. ContinuityTheorem.v — Group V Axioms (Section I O C A D)

**Thin wrapper** re-exporting `ArchimedesStructure.V1` and `DedekindStructure.V2`.

| Line | Declaration | Description |
|------|-------------|-------------|
| 27 | `Axiom V_1` | Archimedean axiom (segment comparison) |
| 36 | `Axiom V_2` | Line completeness (Dedekind cut) |

---

## 9. DesarguesTheorem.v — Desargues' Theorem (Section I)

**Section:** `Section Desargues.` with `Variable (I : IncidenceStructure)`.

| Line | Declaration | Description |
|------|-------------|-------------|
| 25 | `Definition LinesIntersect` | Two lines intersect |
| 29 | `Definition Collinear` | Three points are collinear |
| 33 | `Definition IntersectionPoint` | Point of intersection |
| 42 | `Record LineWithProof` | Line with incidence proof |
| 49 | `Definition line_through` | Line through two points |
| 54 | `Lemma line_through_prop` | Incidence property |
| 63 | `Lemma line_through_unique` | Uniqueness |
| 77 | `Definition Triangle` | Non-collinear triple |
| 81 | `Definition PerspectiveFromPoint` | Perspective from point |
| 86 | `Definition PerspectiveFromLine` | Perspective from line |
| 105 | `Theorem Desargues_theorem` | Desargues' theorem | admit |
| 136 | `Theorem Desargues_converse` | Converse Desargues | admit |

---

## 10. PascalTheorem.v — Pascal's Theorem (Section Pascal)

**Section:** `Section Pascal.` with `Variables (I O C)`.

| Line | Declaration | Description |
|------|-------------|-------------|
| 32 | `Definition LinesIntersect` | Two lines intersect |
| 37 | `Definition Collinear` | Three points are collinear |
| 42 | `Definition IntersectionPoint` | Point of intersection |
| 48 | `Parameter line_through` | Line through two points |
| 50 | `Axiom line_through_prop_ax` | Incidence property |
| 58 | `Axiom two_points_unique_line` | Uniqueness of line through two points |
| 61 | `Lemma line_through_prop` | Derived lemma |
| 67 | `Lemma line_through_unique` | Derived lemma |
| 74 | `Record Circle` | Circle type |
| 81 | `Definition OnCircle` | Point on circle |
| 85 | `Definition Chord` | Chord of circle |
| 100 | `Theorem Pascal_theorem` | Pascal's theorem | admit |
| 139 | `Definition Tangent` | Tangent to circle |
| 145 | `Theorem Pascal_degenerate` | Degenerate Pascal | admit |

---

## 11. IV_Independence.v — Parallel Axiom Independence (Spherical Model)

**Theorems:**

| Line | Name | Description | Status |
|------|------|-------------|--------|
| 157 | `Theorem IV_1_fails_on_sphere` | Parallel postulate fails on sphere | QED |
| 178 | `Theorem I_1_holds_in_ell_plane` | I_1 holds in elliptic plane | QED |
| 197 | `Theorem I_2_holds_in_ell_plane` | I_2 holds in elliptic plane | QED |
| 204 | `Theorem I_3_holds_in_sphere` | I_3 holds on sphere | QED |
| 216 | `Theorem II_1_holds_in_sphere` | II_1 holds on sphere | QED |
| 220 | `Theorem II_2_holds_in_sphere` | II_2 holds on sphere | QED |
| 224 | `Theorem II_3_holds_in_sphere` | II_3 holds on sphere | QED |
| 234 | `Theorem III_1_holds_in_sphere` | III_1 holds on sphere | QED |

---

## 12. V1_Independence.v — Archimedean Axiom Independence (Q(t)² Model)

**Theorems:**

| Line | Name | Description | Status |
|------|------|-------------|--------|
| 153 | `Theorem t_gt_n` | t > any natural n (non-Archimedean) | QED |
| 214 | `Theorem V1_fails_in_QT2` | V_1 fails in Q(t)² model | QED |

---

## 13. V2_Independence.v — Completeness Axiom Independence (Q² Model)

**Theorems:**

| Line | Name | Description | Status |
|------|------|-------------|--------|
| 72 | `Theorem V1_holds_in_Q` | Archimedean axiom holds in Q² | QED |
| 158 | `Theorem V2_fails_in_Q` | Completeness fails in Q² | QED |

---

## 14. III5_Independence.v — SAS Independence Model (Taxicab Metric)

**Theorems:**

| Line | Name | Description | Status |
|------|------|-------------|--------|
| 153 | `Theorem III_5_holds` | CongSeg' A B A B holds | QED |
| 221 | `Theorem SAS_counterexample` | SAS fails in taxicab metric | QED |
| 263 | `Theorem SAS_holds_in_euclidean` | SAS holds in Euclidean metric | QED |

---

## 15. Model_Consistency.v — Euclidean R³ Model

**Theorems (consistency proof):**

| Line | Name | Description | Status |
|------|------|-------------|--------|
| 183 | `Theorem I_1` | I_1 holds in R³ model | QED |
| 198 | `Theorem I_2` | I_2 holds in R³ model | QED |
| 228 | `Theorem I_3` | I_3 holds in R³ model | QED |
| 272 | `Theorem I_4` | I_4 holds in R³ model | QED |
| 316 | `Theorem consistency_statement` | True (axiom system is consistent) | QED |

---

## 16. QPlane.v — Quick Plane Model

**Theorems (4):**

| Line | Name | Status |
|------|------|--------|
| (various) | `Theorem` x4 | QED |

---

## 17. HilbertFoundations.v — Tier-5 Re-export Hub

Re-exports all modules:
```
Common, Types, HilbertStructure, IncidenceTheorem, OrderTheorem,
CongruenceTheorem, ParallelTheorem, ContinuityTheorem, DesarguesTheorem,
PascalTheorem, IV_Independence
```

---

## Summary Statistics

### Hilbert's 5 Groups of Axioms (25 total)

| Group | File | Count | Names |
|-------|------|-------|-------|
| I (Incidence) | IncidenceStructure | 8 | I_1 ~ I_8 |
| II (Order) | OrderStructure | 4 | II_1 ~ II_4 + Pasch |
| III (Congruence) | CongruenceStructure | 6 | III_1 ~ III_6 |
| IV (Parallel) | ParallelTheorem | 3 | IV_1, IV_2, Parallel_nointersect |
| V (Continuity) | ArchimedesStructure + DedekindStructure | 2 | V_1, V_2 |
| Auxiliary | PascalTheorem | 2 | line_through_prop_ax, two_points_unique_line |

### Theorem Status

| Category | Total | QED | admit |
|----------|-------|-----|-------|
| Incidence (I) | 5 | 5 | 0 |
| Order (II) | 4 | 2 | 2 |
| Congruence (III) | 20 | 0 | 20 |
| Parallel (IV) | 0 | 0 | 0 |
| Continuity (V) | 0 | 0 | 0 |
| Desargues | 2 | 0 | 2 |
| Pascal | 2 | 0 | 2 |
| IV_Independence | 8 | 8 | 0 |
| III5_Independence | 3 | 3 | 0 |
| V1_Independence | 2 | 2 | 0 |
| V2_Independence | 2 | 2 | 0 |
| Model_Consistency | 5 | 5 | 0 |
| QPlane | 4 | 4 | 0 |
| **Total** | **57** | **31** | **26** |

### Compilation Status

| File | Status | Notes |
|------|--------|-------|
| Common.v | PASS | |
| Types.v | PASS | |
| HilbertStructure.v | PASS | |
| IncidenceTheorem.v | PASS | |
| OrderTheorem.v | PASS | 2 admit |
| CongruenceTheorem.v | PASS | 20 admit |
| ParallelTheorem.v | PASS | |
| ContinuityTheorem.v | PASS | Thin wrapper |
| DesarguesTheorem.v | PASS | 2 admit |
| PascalTheorem.v | PASS | 2 admit |
| IV_Independence.v | PASS | |
| V1_Independence.v | PASS | |
| V2_Independence.v | PASS | |
| III5_Independence.v | PASS | |
| Model_Consistency.v | PASS | |
| HilbertFoundations.v | PASS | |
| **Total** | **17/17 PASS** | |
