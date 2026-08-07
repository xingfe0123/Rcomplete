# HeineBorelLimitPoint — Heine-Borel Theorem in Rocq

Formalization of the Heine-Borel theorem and limit point compactness equivalence in R^n, using Rocq 9.1.1 Stdlib.

## Theorem

For a subset E of R^n, the following are equivalent:

1. **E is closed and bounded**
2. **E is compact** (every open cover has a finite subcover)
3. **Every infinite subset of E has a limit point in E**

## Key Results

### Main Theorems
- `Heine_Borel_Rn`: `compact K <-> closed K /\ bounded K`
- `compact_limit_point_equiv`: `compact K <-> (∀ E ⊆ K, infinite E → ∃ p, limit_point K E p)`

### Core Lemma (fully proved)
- `infinite_subset_has_limit_point`: Every infinite subset of a compact set has a limit point — proved by contradiction using the pigeonhole principle.

## Dependencies

- **Rocq ≥ 9.1.1** (or Coq 8.16+ with compatible Stdlib)
- **Rocq Stdlib** (included with Rocq installation)

### Installing Rocq

**Option 1: opam (recommended)**
```bash
opam switch create 9.1.1
opam install coq
```

**Option 2: conda**
```bash
conda install -c conda-forge rocq
```

**Option 3: from source**
```bash
git clone https://github.com/rocq/rocq.git
cd rocq
git checkout v9.1.1
./configure
make -j$(nproc)
make install
```

### Verifying Installation
```bash
coqc --version  # Should print Rocq version 9.1.1
```

## Build

### Quick Build
```bash
cd topology
coqc -Q . Topology HeineBorelLimitPoint.v
```

### Using _CoqProject
```bash
cd topology
coqc -R . Topology HeineBorelLimitPoint.v
```

### Clean Build Artifacts
```bash
rm -f *.vo *.vos *.vok *.glob *.aux .lia.cache
```

### Expected Output
```
Warning: Alternatives to Fin.t are available...
[warn-library-file-stdlib-vector, ...]
```
This warning is harmless and does not affect correctness.

## Proof Structure

The equivalence chain is established as follows:

```
compact K
  → compact_imp_limit_point (proved)
  → infinite_subset_has_limit_point (proved, core argument)
  → limit point property

compact K
  → compact_implies_closed (admitted) + compact_implies_bounded (admitted)
  → closed K /\ bounded K

closed K /\ bounded K
  → bounded_implies_in_cube (proved)
  → k_cube_compact (admitted, bisection method)
  → closed_subset_of_compact (admitted)
  → compact K
```

## Status

- **14 lemmas/theorems fully proved**
- **8 technical lemmas marked Admitted** (proof frameworks established, analysis details remaining)
- **All main theorems stated and proof structure complete**

## Design Choices

- **L∞ norm** instead of Euclidean norm (simplifies analysis, avoids square roots)
- **Subspace topology** for relative compactness (`open_in_K`)
- **Classical logic** via `Classical_Prop` and `ClassicalEpsilon`
- **Custom `fin_max_aux`** for computing max over `Fin.t n` (Stdlib's `Fin.fold_nth` not available)

## File Structure

```
topology/
├── HeineBorelLimitPoint.v    # Main development (730 lines)
├── _CoqProject               # Project configuration (-Q . Topology)
├── README.md                 # This file
├── LICENSE                   # MIT License
└── .gitignore                # Ignore compiled artifacts
```

## Admitted Lemmas

The following 8 lemmas are marked `Admitted` with proof frameworks established:

| Lemma | What's Needed |
|-------|---------------|
| `compact_implies_bounded` | Extract max radius from finite subcover (list dependent types) |
| `compact_implies_closed` | Extract min radius from finite subcover |
| `closed_subset_of_compact` | Subspace topology type conversion |
| `k_cube_compact` | Bisection method proof |
| `k_cube_infinite_limit_point` | Bisection method proof |
| `k_cube_bounded` | Norm estimation with fin_max |
| `k_cube_closed` | Closed interval property in R |
| `k_cube_compact_via_HB` | Depends on above |

## References

- Rudin, *Principles of Mathematical Analysis*, Theorem 2.41
- Tao, *Analysis II*, Heine-Borel theorem
- Rocq Standard Library: `Reals`, `Fin`, `List`, `Lra`, `Lia`

## License

MIT License — see [LICENSE](LICENSE) for details.

## Contributing

Contributions to fill in the admitted lemmas are welcome! The main blockers are:
1. Dependent type manipulation for extracting values from existentials over lists
2. Simplification of `fin_max_aux` expressions
3. Subspace topology reasoning (`open_in_K C U` vs `open_in_K K U`)
