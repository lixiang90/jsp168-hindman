# Verified building blocks for the original inverse proof

These four modules prove algebraic orbit identities, finite Hadamard conjugation,
finite Taylor translation, and bounded Lipschitz complex extension. They are
auxiliary results: neither the geometric same-step realization nor the uniform
finite native model family is established by this checkpoint. StrongConjecture
remains incomplete.

Lean 4.32.2 and the repository's pinned mathlib are used. All imported OAI modules
are already present in baseline commit cec91d6971eea09f5ec9d4c66a80c7cbbb355069;
no unverified upstream port is needed for these four files.

Reproduce at the repository root:

```
lake build Hindman168.OriginalSameStepLinearizationOrbit Hindman168.OriginalSameStepLinearizationConjugation Hindman168.OriginalSameStepLinearizationTaylor Hindman168.OriginalFiberMetricExtension
lake env lean --trust=0 -DautoImplicit=false verification/original-inverse-building-blocks/CheckAllAxioms.lean
```

The accompanying audit checks every declaration in these modules against the
allowlist `propext`, `Classical.choice`, `Quot.sound`. The manifest records exact
source SHA256 hashes. No sorry or additional axiom is used.
