# Original-step algebraic linearization

This layer proves a step-s polynomial/time Lie algebra, its terminating lower
central series, finite-dimensionality, finite Taylor translation, and the BCH
conjugation and semidirect-product identities. For real polynomial inputs it
constructs an exact based orbit for every integer time, with the fixed readout
being evaluation at zero. The rational lattice and clock lemmas are included.

These are algebraic building blocks. A uniform finite family of compact native
nilmanifolds, compatible lattice/quotient metrics and uniform Lipschitz bounds
still have to be assembled. The higher-order native interval inverse and
`Hindman168.StrongConjecture` remain unproved.

The 17 local modules reuse the original filtration and adapted-polynomial types.
Small official calculus/basis proofs are attributed in their source files and
moved to independent namespaces. The 312-module official import closure uses
OpenAI math commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; 288 modules are
byte-identical to repository baseline `cec91d6971eea09f5ec9d4c66a80c7cbbb355069`.
The 24 additions include the proved tensor-induction compatibility helper.
The full 2,100-module AxisCompression closure is a separate unfinished build.

Reproduce with Lean 4.32.2 and the repository's pinned mathlib:

```
lake build Hindman168.OriginalSameStepLinearizationRealOrbit Hindman168.OriginalSameStepLinearizationVariable
lake env lean -j1 --trust=0 -DautoImplicit=false verification/original-same-step-algebra/CheckAxioms.lean
lake env lean -j1 --trust=0 -DautoImplicit=false verification/original-same-step-algebra/CheckUpstreamAxioms.lean
```

The source checks explicitly use `autoImplicit=false`; both audits inspect every
declaration in the stated module sets, including private/generated declarations.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Exact source
hashes, options and audit counts are recorded in `manifest.json`.
