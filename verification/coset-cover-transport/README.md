# Observable transport on actual coset covers

`CosetCoverObservableTransport.lean` constructs the actual map of coset
spaces induced by a group homomorphism with lattice containment. No
normal-subgroup assumption is needed. It proves continuity, surjectivity
when the group map is surjective, exact integer linear-orbit identities,
unit-bound preservation, and equality of the finite correlation values.
The final theorem lifts an actual linear orbit and continuous observable
to the cover while preserving every sequence value.

A Lipschitz bound on the actual cover map is an explicit premise, and its
constant multiplies the observable's Lipschitz constant. This module does
not prove that metric bound for a specific BCH cover, realize the bounded
rational model signatures as geometric models, or linearize a polynomial
orbit. Those remain separate obligations; no inverse theorem is asserted.

## Reproduce

Use the unchanged Lean 4.32.2 and locked mathlib revision:

```sh
lake build Hindman168.CosetCoverObservableTransport
lake env lean --trust=0 Hindman168/CosetCoverObservableTransport.lean
lake env lean --trust=0 verification/coset-cover-transport/Axioms.lean
```

The focused build succeeded with 1,869 jobs. The source was subsequently
re-elaborated without messages. All nine theorem axiom sets are subsets of
`propext`, `Classical.choice`, and `Quot.sound`; source hashes are recorded.
These are focused author-side checks, not external peer review or a full
independent kernel replay of imported artifacts.

The new file is not registered in the canonical imports or the unchanged
original 3,059-file snapshot manifest. The original snapshot hashes were
separately rechecked. The main theorem remains unproved, and no competing
proof dependency was added.
