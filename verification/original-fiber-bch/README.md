# BCH subgroup quotient metric comparison

`OriginalFiberMetricBCH` proves an antilipschitz bound for the map from a compact
BCH subgroup quotient into an ambient quotient, under the exact inverse-image
lattice condition and a split linear inclusion. Both metrics are the actual BCH
quotient metrics. This is one geometric building block; the finite native model
family, same-step linearization, and final StrongConjecture remain unfinished.

This layer adds eight official OpenAI modules from commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` under the existing Apache-2.0 license
in `dependencies/openai-finite-szemeredi/LICENSE`. The other 288 modules in their
296-module import closure were already in the baseline repository. Two files
have compatibility-only lemma renamings, marked in their file headers.

Lean 4.32.2, mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`.

```
lake build Hindman168.OriginalFiberMetricBCH
lake env lean --trust=0 -DautoImplicit=false verification/original-fiber-bch/CheckUpstreamAxioms.lean
lake env lean --trust=0 -DautoImplicit=false verification/original-fiber-bch/CheckAxioms.lean
```

The audits check every declaration against the standard three-axiom allowlist.
The summary is retained instead of the long per-declaration transcript. Exact
source hashes and the upstream import closure are recorded in `manifest.json`.
