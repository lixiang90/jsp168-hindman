# Finite conclusion implies the full rapid-separation statement

The two new modules prove an elementary reduction between the repository's
existing, unchanged statements:

```lean
Hindman168.finite_implies_strong
  (h : Hindman168.FiniteConjecture) : Hindman168.StrongConjecture

Hindman168.finite_iff_strong :
  Hindman168.FiniteConjecture ↔ Hindman168.StrongConjecture
```

The hypothesis `FiniteConjecture` is explicit and remains unproved in this
repository. This implication is not a proof of either conjecture. No external
finite sums/products proof is imported by these modules.

## Argument and parameters

`QuantitativeSeparation.lean` constructs a finite auxiliary coloring from an
integer floor of a positive multiple of `log(log n)`, modulo a fixed positive
integer. If `1 < a ≤ b ≤ a^E`, the log-log increment between `b` and `a*b` is
bounded below by `log(1+1/E)` and above by `log 2`. The coloring distinguishes
these two numbers. Thus a refined monochromatic finite-products witness has
pairwise gaps `a^E < b`.

`FiniteToStrong.lean` refines the original coloring by that finite coloring,
uses an oversized finite witness, and removes its finitely many small values.
An increasing enumeration preserves all nonempty subset sums and products.
It then takes `E = m*D+1` and a cutoff above
`max 2 (R*(m+1)^D)`. Bounds on the sum and product of predecessors yield the
exact separation in the original `StrongWitness`, including its first index.
The original definitions and their parameter ranges were not weakened.

## Reproduce and evidence

Use the repository's unchanged Lean 4.32.2 and locked mathlib revision:

```sh
lake build Hindman168.FiniteToStrong
lake env lean Hindman168/QuantitativeSeparation.lean
lake env lean Hindman168/FiniteToStrong.lean
lake env lean verification/finite-to-strong/Axioms.lean
```

The targeted Lake build succeeded, and both source files were subsequently
re-elaborated directly. `build.txt` records the commands and output. All nine
new theorems were checked with `#print axioms`; their reports in `axioms.txt`
contain only `propext`, `Classical.choice`, and `Quot.sound`. The additional
source and audit-script hashes are recorded in `source-hashes.json`.

These are independently checked additions. They are not yet imported by
the canonical `Hindman168.lean` or registered in `Verification.lean`.
The original 3,059-file `verification-manifest.json` does not cover them;
that original checkpoint's source hashes were separately rerun successfully.
No full-project build or full imported-library kernel replay is claimed by
these focused checks. A complete finite sums/products proof is still needed
before this bridge can provide an unconditional strong theorem.
