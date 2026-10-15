# Original inverse normalization: verified local lemmas

This checkpoint adds numerical parameter choices and the exact interval/periodic
mean normalization used by the original inverse interface. It does not establish
the native inverse theorem, a bounded finite family of native nilmanifolds, or
same-step linearization. The original StrongConjecture endpoint remains incomplete.

Baseline: cec91d6971eea09f5ec9d4c66a80c7cbbb355069.
Toolchain: Lean 4.32.2; mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.

Reproduce from the repository root after `lake exe cache get`:

```
lake build Hindman168.OriginalInverseNormalizationNumerics Hindman168.OriginalInverseNormalizationMean
lake env lean --trust=0 -DautoImplicit=false verification/original-inverse-normalization/CheckAllAxioms.lean
```

The audit enumerates every declaration in the two modules and rejects every axiom
other than `propext`, `Classical.choice`, and `Quot.sound`. Source hashes and local
verification results are recorded alongside this file. No new axiom or sorry is used.
