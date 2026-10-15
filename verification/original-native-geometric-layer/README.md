# Finite native models and same-step geometric linearization

The original finite-family/linear-orbit geometric interface is now proved.
`Hindman168.OriginalBoundedNativeModels.exists_finite_native_linear_menu`
chooses a finite nonempty family of genuine step-bounded native nilmanifolds
and a common Lipschitz bound before the bounded rational model, niltest,
polynomial coefficients, or integer sampling interval is supplied. Every
integer evaluation is preserved by a linear orbit on the stated quotient.
The construction retains the original quotient metrics, unit observable
bound, and original step; no replacement model predicate or extra axiom is used.

The twelve new local modules prove finite coded models, exact filtered and
metric transport, rational fiber metric control, compact same-step models,
observable extension, and the uniform finite linear menu. Their complete
540-module official import closure and the existing rational-code helper
were included in one strict kernel/axiom audit: 553 modules, 14,338 declarations.
All axioms are among `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduce

Use the pinned `lean-toolchain` and `lake-manifest.json` from this repository.
After obtaining the matching mathlib cache, run from the repository root:

```sh
lake build Hindman168.OriginalBoundedNativeModelsLinearMenu Hindman168.OriginalFiberMetricRational
lake env lean -j1 --trust=0 -DautoImplicit=false verification/original-native-geometric-layer/CheckAxioms.lean
```

The audit enumerates every declaration, including generated/private helpers,
in all 553 named modules and rejects a missing module or nonstandard axiom.
`manifest.json` records exact source hashes, fixed upstream source, and the
two narrowly trimmed official imports. Modified upstream files carry notices;
the existing Apache-2.0 license remains under `dependencies/openai-finite-szemeredi`.
The original registered 3,059-file snapshot hashes are unchanged.

## Remaining boundary

This checkpoint does not prove `HasNativePeriodicIntervalInverse` or the
original `StrongConjecture`. The analytic AxisCompression inverse still
requires its full official closure to compile and be audited on this toolchain,
followed by the exact interval adapter and canonical endpoint replay.
The prepared adapter drafts are not included here. The repository stays private.
