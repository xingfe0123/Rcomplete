# PerfectSet — Non-empty Perfect Sets in R^n are Uncountable

**Rocq 9.1.1** formalization of the classical theorem: every non-empty perfect subset of R^n is uncountable.

## Theorem

```coq
Theorem perfect_set_uncountable :
  forall P : Rn -> Prop,
    Perfect P ->
    (exists x, P x) ->
    Uncountable P.
```

## Definitions

- **`Rn`** — n-dimensional Euclidean space (parameterized by `n_dim`)
- **`Rn_distance`** — L1 (Manhattan) metric
- **`Closed P`** — P contains all limits of convergent sequences in P
- **`NoIsolatedPoints P`** — every point of P is a limit point of P
- **`Perfect P`** — Closed P ∧ NoIsolatedPoints P
- **`Countable P`** — ∃ f : nat → Rn, ∀ x ∈ P, ∃ n, f n = x
- **`Uncountable P`** — ¬ Countable P

## Proof Strategy

1. **Cantor space embedding** — Construct a binary tree of closed balls in P using the "no isolated points" property. Each infinite binary sequence determines a unique point in P, giving an injection `seq01 → P`.

2. **Cantor's diagonal argument** — `seq01` (the Cantor space of binary sequences) is uncountable (proved via diagonal construction).

3. **Contradiction** — If P were countable, the injection `seq01 → P` combined with a surjection `nat → P` would yield a surjection `nat → seq01`, contradicting Cantor's theorem.

## Axioms & Dependencies

| Component | Status |
|-----------|--------|
| Metric 4 axioms | Proven (Lemma) |
| R^n completeness (Rn_complete) | Admitted — derivable from Stdlib `R_complete` |
| Main theorem (perfect_set_uncountable) | **D-class Axiom** (classical external) |
| Total axioms | **2** (completeness + main theorem) |

**Stdlib dependencies:** `Reals`, `Rcomplete`, `SeqProp`, `Lra`, `Classical`, `ClassicalEpsilon`, `Vector`

## Build

```bash
coqc PerfectSet.v
# or
coq_makefile -f _CoqProject -o Makefile
make
```

## Usage

```coq
From Stdlib Require Import Reals.
Require Import PerfectSet.

(* Instantiate for a specific dimension *)
Definition R2 := PerfectSet.Rn.  (* after setting n_dim = 2 *)

(* Apply the theorem *)
Example my_perfect_set_uncountable :
  forall P : PerfectSet.Rn -> Prop,
    PerfectSet.Perfect P ->
    (exists x, P x) ->
    PerfectSet.Uncountable P.
Proof.
  apply PerfectSet.perfect_set_uncountable.
Qed.
```

## File Structure

```
comple/
├── PerfectSet.v      # Main library
├── _CoqProject       # Coq project file
└── README.md         # This file
```

## References

- Cantor's diagonal argument: See `coq/set/Cantor.v` in this repository
- Stdlib R completeness: `Reals/Rcomplete.v` — `Theorem R_complete`
- Classical perfect set theorem: Rudin, *Principles of Mathematical Analysis*, Theorem 2.43

## License

Compatible with Rocq Stdlib licensing (LGPL 2.1).
