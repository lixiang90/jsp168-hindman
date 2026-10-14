# Actual principal counts to finite sums/products witnesses

These three modules implement the final finite extraction in Section 2.5
of the OpenAI paper, using the repository's unchanged definitions of
`principalWeightedColorCount`, `IndexedWitness`, and `MonoFSFP`.

- `PositiveColorCountExtraction` shows that a nonzero weighted integrand
  forces the actual natural-number subset sums and products to share one
  color. Exact integer row scaling is required; auxiliary weights cannot
  create a false positive.
- `PrincipalPositiveCountExtraction` proves the exact equality with the
  existing principal count, then supplies its scaling and divisibility
  conditions eventually from the existing master-parameter hypotheses.
- `PrincipalCountWitness` uses the original harmonic support windows,
  coefficient bounds, and cutoff growth to prove strict increase, without
  an extra injectivity assumption. Its final theorem turns positivity of
  a finite sum of the actual counts at arbitrarily late stages into a set
  of exactly `m+1` positive integers with every nonempty subset sum and
  product in the same color. The witnessing chain, scale, and color may
  vary with the stage.

The main interface is
`MasterParameterConditions.principal_positive_sum_yields_finite_witness`.
Its positive-count hypothesis is explicit and has NOT been proved here.
Thus these results do not prove `FiniteConjecture` or `StrongConjecture`.
They do not assume a finite FS/FP theorem, copy a competing proof, or add
an axiom. The separate checked `FiniteToStrong` bridge can be used only
once the unconditional finite theorem has been proved.

## Reproduce

Keep the unchanged Lean 4.32.2 and locked mathlib revision, then run:

```sh
lake build Hindman168.PrincipalCountWitness
lake env lean Hindman168/PositiveColorCountExtraction.lean
lake env lean Hindman168/PrincipalPositiveCountExtraction.lean
lake env lean Hindman168/PrincipalCountWitness.lean
lake env lean verification/principal-count-extraction/Axioms.lean
```

`build.txt` records the successful focused Lake build (4,673 jobs).
`source-check.txt` records the subsequent direct re-elaboration of all three
sources. `axioms.txt` covers all 11 new theorems, with only `propext`,
`Classical.choice`, and `Quot.sound`; source hashes are recorded separately.

These are focused author-side checks, not external peer review or a full
independent kernel replay of imported artifacts. These new modules are not
yet imported by the canonical `Hindman168.lean` or `Verification.lean`.
The unchanged original 3,059-file `verification-manifest.json` does not
cover them. Its recorded source hashes have been separately rechecked.
The full analytic positivity argument and main theorem remain unfinished.
