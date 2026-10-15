# Compact metric comparison helper

This auxiliary module proves that a continuous injective map on a compact
metric space is globally antilipschitz when it satisfies a local lower metric
bound. A second lemma transports such a lower bound through an open chart.
The application to native nilmanifolds remains to be completed.

Reproduce with Lean 4.32.2 and the pinned mathlib:

```
lake build Hindman168.OriginalFiberMetricCompact
lake env lean --trust=0 -DautoImplicit=false verification/original-fiber-compact/CheckAllAxioms.lean
```

Both declarations pass the standard three-axiom audit. No additional axioms
or sorry are introduced. This checkpoint does not complete StrongConjecture.
