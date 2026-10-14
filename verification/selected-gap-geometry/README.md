# Selected padding-gap geometry

This focused addition separates the prediction padding gap from the principal
raw cutoff while retaining the original ambient master dimension, modulus,
selected scales and actual full raw sampling law.

## Proved interfaces

- `alignmentGeometryWithGap` changes only the gap field. Every master-condition
  hypothesis is still about the original family; no master conditions for the
  changed view are assumed.
- The selected microcell estimates use the padding gap and principal cutoff.
  The exact harmonic-cell comparison transfers a complete-cell uniform union
  lower bound of `3/(4Q)` to the actual harmonic conditional slot sum `1/(2Q)`.
  Partial-cell losses vanish. The empirical probability is identified exactly.
- The short-key posterior, actual native source transport, full CRT means,
  tail removal and all-face estimates use the same source and original raw
  law. The face estimates explicitly restrict letters to `sourcePivot < gap`.
- `selected_alignment_selected_catalogue_cosets` applies to every cofinal
  sequence and positive raw event, and selects one full supported sample,
  common subsequence, joint filtration, period, representatives and smooth
  curve. It supplies both local/alpha Haar laws and actual measure/setwise
  symmetries of all duplicated target projections.
- Actual full-raw exposure stability has vanishing failure mass. The original
  sampled values of unused coordinates are retained. The one-filled selected
  extension is only an algebraic adapter, not a supported raw sample.
- The key representative is selected from supported stable anchors. With
  `0` among the queried slots, frozen labels agree on a good key fiber. The
  resulting per-key recipe functions are fixed before source extraction and
  their readings equal the original padding recipes on the same joint orbit.
- The restricted catalogue symmetries yield common-coordinate letter lifts
  and exact selected native reading equivariance.

## Remaining assembly

The uniform Alignment principle is not proved by these interfaces. The next
step must combine these key recipes, common observable compactness, the fixed
finite-route closed/open comparison and the actual point-mixture law. The
bad fine-conditioning mass must vanish along the ordinary filter by applying
extraction to every cofinal positive bad event. Then the already verified
conditional extension and future-protected pivot path arguments can be
instantiated, with finite scales and the positive mass bound chosen before
models, complexity and threshold. The higher-order inverse remains a separate
open node. No full Hindman theorem is claimed.

## Reproduction and evidence

With the pinned toolchain, run:

```
lake build $(cat verification/selected-gap-geometry/targets.txt)
lake env lean --trust=0 verification/selected-gap-geometry/CheckAllDeclarations.lean
python scripts/verify_snapshot.py
```

The focused build passed 6,834 jobs. The audit enumerates every declaration
owned by these 80 modules, including generated declarations: all 300 use only
`propext`, `Classical.choice`, `Quot.sound`, or a subset. Source hashes,
module list, build/audit logs and verification metadata are included. The
original 3,059 snapshot hashes remain unchanged. Canonical root imports,
original dependency provenance and toolchain pins are unchanged. This is not
a full-project replay or a replay of every imported kernel artifact.
