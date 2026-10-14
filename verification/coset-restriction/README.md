# Product-coset subfamily restriction

`Hindman168/PiCosetRestriction.lean` constructs restriction from the quotient
of a dependent product group by its product subgroup to an indexed subfamily.
The subgroups need not be normal. The five proved results give its coordinate
formula, its value on a group representative, identity and composition laws,
and continuity for topological groups. They use the existing proved product
quotient equivalence; they assume no Haar law, inverse theorem, or alignment
conclusion.

## Reproduce

Use the repository's unchanged Lean 4.32.2 and locked mathlib revision. From
the repository root, run:

```sh
lake exe cache get
lake build Hindman168.PiCosetRestriction
lake env lean verification/coset-restriction/Axioms.lean
```

For this historical mathlib revision, the official legacy cache can also be
selected with `MATHLIB_CACHE_FROM=legacy lake exe cache get` if the first
cache location has no matching files. This does not change dependency pins.

The build and axiom command both exited successfully on 2026-10-14 in a
fresh Linux workspace. `build.txt` and `axioms.txt` record their output.
All five theorem reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. `source-hashes.json` identifies the exact additional source and
check script, their commands, and the unchanged toolchain/dependency pins.

## Scope of the checks

This new module is independently checked. It is not yet imported by the
canonical `Hindman168.lean` or registered in `Verification.lean`.
The existing `verification-manifest.json` covers the original 3,059-file
checkpoint and does not cover this added module. That original checkpoint's
source-hash verifier was also rerun successfully; its whole-project build
and registered axiom audit have not yet been replayed in this workspace.

This result supplies an elementary restriction interface needed for the
heterogeneous joint-source work. Full Alignment, the inverse-theorem gap,
and the finite same-colour sums/products conclusion are not proved by it.
No native-source specialization or uncompiled candidate is included in
these validation claims. The repository remains a private partial project.
