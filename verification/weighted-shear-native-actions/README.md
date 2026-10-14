# Native affine weighted-shear realization

The five added modules extend the seven previously checked weighted-shear group/box-law modules. They use actual weighted total degree, not ordinary degree: vector coefficients at polynomial weight `d` lie in filtration layer `d + offset`; Picard perturbation preserves this offset; a coordinate functional annihilating the next layer turns offset one into strict weighted degree.

The native left-translation polynomial evaluates exactly to `log(exp(v) * exp(Y))`. The affine theorem uses the same original `c` and smooth group homomorphism `φ`, with its actual differential and exponential naturality, and realizes `log(c * φ(exp(Y)))` in the proved weighted-shear group. Its inputs explicitly include bracket-compatible filtration, adapted basis, `log(c) ∈ F 1`, and the actual graded-identity condition. This batch does not construct those geometric inputs.

Filtered transfer proves that the explicit formula `u + R(T(Pu) - Pu)` is a weighted shear when `P` and `R` preserve the stated filtrations. That theorem alone does not assert `P ∘ R = id`, so projected equivariance requires the separate constructed-right-inverse bridge. Haar weak-limit identification, the same-source geometric image/cube interface, and the final uniform alignment principle are outside this batch.

Both terminal Lake targets passed. All five new sources were independently re-elaborated with `lake env lean --trust=0`. The 129 declarations across all twelve files were individually printed and checked against the complete declaration manifest; only `propext`, `Classical.choice`, and `Quot.sound` occur. Source hashes identify exactly what was checked. Original pins/canonical imports/verification manifest remain unchanged.
