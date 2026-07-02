# Hopf Lemma Formalization Plan (Path B)

## 1. Theorem (Ladyzhenskaya 1968, Chapter III, Section 3, Lemma 3.1)

**Parabolic Hopf Boundary Point Lemma**:
Let L be a uniformly parabolic operator, Lu >= 0 in Q_T = Omega x (0, T].
u in C^{2,1}(Q_T) intersect C^0(bar Omega x [0,T]).
c(x,t) <= 0 in Q_T.
u attains a non-negative maximum at a side boundary point (x0, t0) in partial Omega x (0, T].
Omega satisfies the interior sphere condition at x0.
Then the inward normal derivative partial u / partial nu (x0, t0) > 0.

**Weak Maximum Principle** (derived from Hopf):
If Lu >= 0 in Q_T and c <= 0, then max_{Q_T} u = max_{partial' Q_T} u.

**Uniqueness** (derived from weak maximum principle):
Two solutions u1, u2 with same PDE + initial data => u1 = u2.

## 2. Scope (Path B)

- Parabolic operator abstraction (Parameter + Axiom)
- Interior sphere condition (Definition)
- Parabolic Hopf Lemma (Axiom)
- Weak Maximum Principle (Axiom)
- Uniqueness (Axiom + QED theorem)
- Connection to LadyzhenskayaMain

**Lines**: ~192
**Axioms**: 11 (3 core + 8 supporting)
**Estimated time**: 3-5 days (already completed in this session)

## 3. Dependencies

- Coq 8.18 + Reals library
- LadyzhenskayaMain types (ParabolicProblem, ParabolicHolderSpace, etc.)
  - Abstracted as Parameters to avoid cross-project dependency

## 4. Axiom Breakdown

| Category | Axioms | Notes |
|----------|--------|-------|
| Core | 3 | hopf_parabolic, weak_maximum_principle, parabolic_uniqueness |
| Metric | 4 | Omega_distance properties |
| Time | 1 | T_horizon_pos |
| Derivative | 1 | directional_derivative_in_normal |
| Geometry | 2 | coeff_c_nonpos, normal_direction |

## 5. Proof Structure

```
hopf_parabolic (Axiom)
    |
    v
weak_maximum_principle (Axiom)
    |
    v
parabolic_uniqueness (Axiom)
    |
    v
schauder_global_uniqueness_from_hopf (QED)
```

## 6. Connection to LadyzhenskayaMain

| LadyzhenskayaMain | Hopf.v replacement |
|-------------------|-------------------|
| parabolic_max_principle (Axiom) | weak_maximum_principle (Axiom) |
| schauder_global_uniqueness (Axiom) | schauder_global_uniqueness_from_hopf (QED) |

## 7. Next Steps (if extending to Path C)

- Prove weak_maximum_principle from hopf_parabolic (requires linearity of L)
- Prove parabolic_uniqueness from weak_maximum_principle (requires boundary value analysis)
- Formalize interior sphere condition in R^n (not just abstract Type)
- Add C^{2,1} regularity assumptions
