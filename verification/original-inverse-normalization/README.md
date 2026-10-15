# Original inverse normalization: verified local lemmas

This checkpoint records four modules:

- `OriginalInverseNormalizationNumerics`: fixed logarithmic threshold, complexity
  and positive correlation budgets, doubled-interval density, and no wraparound.
- `OriginalInverseNormalizationMean`: the exact `Unit → ℤ` interval encoding,
  cardinality, finite complex mean, periodic mean, and pair-sum reflection.
- `OriginalInverseNormalizationEmpty`: evaluation of the totalized interval
  definitions at zero, and exclusion of zero length or zero period count from a
  positive Gowers-norm hypothesis.
- `OriginalInverseNormalizationTransport`: the additive equivalence with `ℤ`,
  exact supported-cube Gowers-norm transport, representatives, pair-sum reflection,
  and density for the actual cyclic encoding.

These are normalization lemmas, not a proof of the native inverse theorem. They
retain the existing definitions and actual cube-count normalization. This layer
alone does not supply the bounded finite family of native nilmanifolds or the
same-step linearization. The original StrongConjecture endpoint remains incomplete.

Baseline: `cec91d6971eea09f5ec9d4c66a80c7cbbb355069`.
This extends the two-module normalization checkpoint
`1487aabb3ca4267aa69e8265e2fa66842610e183`.
Toolchain: Lean 4.32.2 (commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`);
mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`.

Reproduce from the repository root after `lake exe cache get`:

```sh
lake build Hindman168.OriginalInverseNormalizationNumerics Hindman168.OriginalInverseNormalizationMean Hindman168.OriginalInverseNormalizationEmpty Hindman168.OriginalInverseNormalizationTransport
lake env lean -j1 --trust=0 -DautoImplicit=false verification/original-inverse-normalization/CheckAllAxioms.lean
```

The source build uses the repository's `autoImplicit = false` option. The audit
passes it explicitly as well: `lake env lean` alone does not apply `leanOptions`.
The recorded unified audit was run with the main repository's actual build
artifacts first on `LEAN_PATH`, without any scratch API or substitute definitions.

The audit enumerates every declaration in these four target modules, including
generated auxiliary declarations, and rejects every axiom other than `propext`,
`Classical.choice`, and `Quot.sound`. On 2026-10-15 it passed all 54 declarations
with trust level zero. This count is for the four targets, not their entire import
closure. Both new modules compiled against their unchanged production imports.
Exact source hashes, artifact hashes, and verification commands are in
`manifest.json`; the complete audit output is `axioms.log`. No new axiom or sorry
is used.
