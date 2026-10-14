# Finite bounded rational model signatures

`Hindman168/BoundedRationalModelCodes.lean` independently proves that a
single finite list covers every signature with bounded dimension, integer
grid scale, and numerator/denominator bounds on its rational coordinates.
The coordinates include Lie structure constants and padded filtration
layer bases. The list is fixed by these bounds before an input signature
is chosen. Its finiteness is constructed, not assumed.

This is a finite enumeration lemma. It does NOT construct a finite family
of native nilmanifolds, prove the inverse theorem, or provide polynomial
to linear orbit conversion. Covering-lattice realization, geometric data,
and metric/Lipschitz transport remain separate obligations. No competing
proof dependency or new axiom is introduced.

## Reproduce

Use the unchanged Lean 4.32.2 and locked mathlib revision:

```sh
lake build Hindman168.BoundedRationalModelCodes
lake env lean --trust=0 Hindman168/BoundedRationalModelCodes.lean
lake env lean --trust=0 verification/bounded-model-codes/Axioms.lean
```

The focused build succeeded with 818 jobs. The source was subsequently
re-elaborated, and all three theorem axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The recorded empty `source-check.txt`
means the direct source check emitted no messages; its exit code was zero.
Only seven specific mathlib modules are imported.

These author-side checks are not external peer review or a complete
independent kernel replay. This addition is not registered in the canonical
project imports or the unchanged original 3,059-file snapshot manifest.
The original snapshot hashes were separately rechecked. The main finite
sums/products theorem remains unproved.
