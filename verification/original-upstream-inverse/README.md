# Current verified official inverse closure

This directory tracks the current verified portion of the pinned official
OpenAI inverse proof. It is updated in place as the complete closure advances.
The current dependency-closed set contains 1042 OAI modules and 20,689 declarations.
Strict source checks succeeded with `autoImplicit=false`; a unified kernel/axiom
check with `--trust=0` accepted only `propext`, `Classical.choice`, and `Quot.sound`.
The source and compiled-artifact hashes stayed unchanged across that check.

The complete fixed-source AxisCompression closure has 2,100 modules. This
checkpoint does not build that endpoint or prove the original StrongConjecture.
The finite native geometric menu and exact same-step linearization are recorded
separately in [the geometric layer](../original-native-geometric-layer/README.md).

## Reproduce

Use this repository's pinned Lean 4.32.2 and mathlib revision. From its root:

```sh
xargs lake build < verification/original-upstream-inverse/modules.txt
lake env lean -j1 --trust=0 -DautoImplicit=false verification/original-upstream-inverse/CheckAxioms.lean
```

`manifest.json` identifies every source hash, its direct OAI imports, and its
comparison with OpenAI commit adc7f1241b42e322a6451854ab7e4b4c146bf78a. Modified
upstream files carry compatibility notices; the upstream Apache-2.0 license and
attribution remain under `dependencies/openai-finite-szemeredi`. The audit checks
all declarations defined in the listed modules, including private/generated
helpers. External Mathlib/Lean modules are not counted as explicit audit targets.

The remaining analytic closure, final interval adapter, canonical imports and
full original-target replay still have to pass. The repository remains private.
