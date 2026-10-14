# Weighted polynomial shears and asymptotically invariant box laws

The seven `WeightedShear...` modules prove the algebraic and weighted-box
parts of Lemma 7.7, including equations (7.19) and (7.20), independently
from the actual native Lie/BCH realization still needed by Alignment.

## Proved statements

- The filtration is defined on actual multivariate polynomials by weighted
  monomial degree. Negative levels are zero, and coordinate substitutions
  with strict degree drop are proved bijective with strict-shear inverses.
- These automorphisms form a group with a genuine central filtration. If
  every coordinate weight is at most `s`, its lower central series at `s`
  is trivial. The bound is independent of dimension and coefficients.
- Inverse substitution gives the actual group action on real coordinate
  space, with a proved polynomial homeomorphism for each group element.
- The action preserves Lebesgue measure, proved by decomposing it into
  weight layers of conditional translations, rather than assuming a
  volume-preserving action or a recurrence property.
- The original boxes have coordinate widths `E^(weight i)`. Actual
  polynomial coefficient estimates bound their displaced images and
  relative symmetric differences. The estimate for a fixed shear is
  `2 * ((1 + C/E)^dimension - 1)`, with `C` depending on that shear.
- `weightedShearBoxLaw_finite_uniform` gives a single large-`E` threshold
  for every shear in a fixed finite list and every measurable event. Thus
  the normalized box laws and their pushforwards converge in total
  variation. The finite-list uniformity does not assert one bound uniform
  over all possible shears or coefficients.

Positive coordinate weights, a finite coordinate type for the box/measure
results, and the stated upper weight bound are explicit. Bijectivity,
nilpotence, measure preservation, and the asymptotic estimate are proved.

## Important remaining boundary

This does NOT prove all of Lemma 7.7 or the full Alignment theorem. It does
not yet show that the required native Lie/BCH transformations are these
strict weighted polynomial shears, nor construct the needed Haar weak
limit or the full recurrence argument. The GTZ inverse work and main
finite sums/products theorem also remain unfinished. No competing proof
dependency, new axiom, or claim of completion is included.

## Reproduce

Keep the unchanged Lean 4.32.2 and locked mathlib revision:

```sh
lake build Hindman168.WeightedShearBoxLaw
lake env lean verification/weighted-shear-box-laws/Axioms.lean
```

The focused build completed successfully with 3,181 jobs. All seven source
files were subsequently re-elaborated individually; `source-check.txt`
records those commands and output. `Axioms.lean` covers all 73 listed
new declarations, with axiom sets contained in `propext`,
`Classical.choice`, and `Quot.sound`. Source hashes are recorded separately.

These are focused author-side checks, not external peer review or a full
independent kernel replay of imported artifacts. The canonical project
imports and original 3,059-file manifest remain unchanged; these additions
are not yet covered by that original manifest. Its original hashes were
separately rechecked.
