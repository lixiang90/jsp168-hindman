# Exact interval cube zero-extension

`Hindman168/IntegerIntervalCubeZeroExtension.lean` supplies the exact
normalization bridge between the repository's integer interval cube mean
and a zero-extended function on a finite cyclic group.

For a nonempty interval `[0,L)` and ambient modulus `M > 2*(L-1)`, it proves:

- A genuine bijection between integer interval cubes and cyclic cubes whose
  every vertex lies in the interval, preserving every vertex value.
- Equality of the unnormalized cube sums and the precise ambient average.
- The interval cube mean equals the cyclic cube mean divided by the cyclic
  cube mean of the interval indicator. This is an identity at the cube-power
  level; it is not a claim that the raw means have equal denominators.
- The indicator denominator is positive.
- Every real input has nonnegative interval cube mean in positive dimension,
  by applying finite cyclic cube positivity to that exact normalization.

The input period `q` and ambient modulus `M` are independent. The no-wrap
bound is independent of dimension. No inverse theorem, large-norm premise,
long-period approximation, or conjectural analytic input is assumed.

## Reproduce

Keep the repository's existing Lean 4.32.2 and locked mathlib revision:

```sh
lake exe cache get
lake build Hindman168.IntegerIntervalCubeZeroExtension
lake env lean verification/interval-zero-extension/Axioms.lean
```

For this historical mathlib revision, its official legacy cache is available
via `MATHLIB_CACHE_FROM=legacy lake exe cache get` if needed.

The targeted build completed successfully with 4,219 jobs on 2026-10-14.
`build.txt` contains that build output. All 21 definitions and theorems in the
module were then checked with `#print axioms`; `axioms.txt` is the output.
Their axiom sets are subsets of `propext`, `Classical.choice`, and `Quot.sound`.
The additional source and audit-script hashes are in `source-hashes.json`.

## Verification boundary

This module is independently checked and is not yet added to the canonical
`Hindman168.lean` or `Verification.lean`. The original 3,059-file
`verification-manifest.json` does not cover this addition. Its original
source hashes were separately rerun and passed without changing those files.

The new theorem closes a normalization gap needed before applying an interval
inverse theorem. It does not prove the arbitrary-input linear nilsequence
inverse theorem, Alignment, or the final sums/products theorem. A complete
project build and all originally registered axiom checks have not yet been
replayed in this workspace. This is not an independent kernel replay of all
imported mathlib artifacts or a prize-completion certificate.
