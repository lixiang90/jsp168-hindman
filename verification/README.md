# Current proof dependency overview

The full `Hindman168.StrongConjecture` is **not proved**. Keep the repository
private. This overview distinguishes proved interfaces from the remaining
analytic inputs; it does not replace or broaden the original snapshot audit.

## Verified final route

1. `principal_product_chain_selection` supplies a suitable finite `n` and
   the product-chain selector from the existing selection theorem.
2. For fixed finite scales `B,A` and positive `delta`,
   `principal_final_deduction_tolerances` chooses `theta,eta` before models.
   Given the exact original `PrincipalPredictionLimitData`, unit-range
   models, admissible parameters, and the specified adding-pair-event
   liminf, it proves a positive distinct same-color FS/FP set of size `m+1`.
   See [the final deduction audit](positive-principal-sum/README.md).
3. The actual count-to-witness extraction is separately verified in
   [principal-count-extraction](principal-count-extraction/README.md).
4. Once the finite theorem is obtained for every coloring and requested
   size, `finite_implies_strong` yields the unchanged rapid-separation
   statement. `finite_iff_strong` is proved, but neither side is yet proved
   unconditionally. See [finite-to-strong](finite-to-strong/README.md).

The existing `exists_masterParameterFamily` constructs admissible master
parameters under its explicit positivity/nonzero input conditions. The
remaining work must choose compatible data with the required quantifier
order, rather than replace either analytic principle by a new assumption.

## Exact remaining analytic nodes

### A. Prediction / Principle 2.3

The existing prediction construction still needs
`HasNativePeriodicIntervalInverse s k` at the required higher Gowers orders
(the current model interfaces use `k = 2^d + 2^d - 1`). It must supply a
finite list of genuine native step-bounded nilmanifolds, Lipschitz bounds,
and a positive correlation constant BEFORE the cyclic order, interval
length, and arbitrary bounded input are chosen, with a LINEAR orbit.

Proved prerequisites include exact interval/cyclic cube normalization,
finite bounded rational signatures, and exact observable transport on
actual coset covers. The exact original OpenAI supported-cube norm interface
is now integrated and audited in [supported cubes](supported-cube-interface/README.md);
the genuine first-order native inverse is proved in
[rooted normalization and U1](interval-rooted-and-one/README.md). See [zero extension](interval-zero-extension/README.md),
[model signatures](bounded-model-codes/README.md), and
[cover transport](coset-cover-transport/README.md).

Still needed: compatible integration of the upstream GTZ theorem dependency
closure, realization of the
finite signatures as a uniform finite native model family with actual
lattice/metric bounds, and polynomial-to-linear orbit conversion preserving
the required step. Signatures alone are not geometric models; a polynomial
nilsequence inverse alone is not this linear finite-list interface.

### B. Uniform Alignment / Principle 2.4

For fixed `n,r,s`, construct finite `B,A` and `delta > 0` depending only on
those parameters. For every admissible family, actual step-at-most-`s`
model system, and positive threshold, prove the alignment-event liminf is
at least `delta`, independent of threshold and model complexity.

Verified geometric prerequisites now include one full heterogeneous joint
source extraction with all target measure/setwise symmetries on the SAME
sample, subsequence, filtration, period, rational representatives and smooth
curve; actual image-filtration cube identification; native covering/lifting,
graded identities, adapted bases and right inverses; common-coordinate
weighted affine lifts; and the actual joint `h H rho` Haar-image weak limit
for every fixed shear/word. The actual integer point-orbit empirical
probabilities also have their retained mixture weak limit. See
[native joint geometry](native-joint-geometry/README.md).

The finite-route closed/open mass deduction, exact same-joint frozen-piece
readings, original-master harmonic shift removal and abstract conditional
pivot product are now verified in
[principal native mass](principal-native-mass/README.md).

The common uniform observable limits now preserve the same joint laws, and
actual future-scale threshold paths imply the exact final alignment event;
see [future thresholds and observables](future-threshold-and-observables/README.md).

The remaining realization chain is:

- Feed the concrete Alignment slot transformations and the proved target
  symmetries into those common-coordinate lift theorems, then interpret the
  finite recurrence routes and actual frozen-piece readings on that same
  joint space.
- Instantiate the proved closed/open threshold and Portmanteau argument
  to obtain good-conditioning shifted success with vanishing bad mass.
  Supply the secured local thresholds along the actual future-protected
  paths, then apply the proved event identification, harmonic extension
  and finite-pivot mass product. Stronger prelimit Boolean-palette
  equality is not a necessary input.
- Assemble the uniform principle with finite scales and a positive lower
  bound chosen before models, padding, complexity and threshold.

The exact `HasAlignmentMonomialRecurrence s` input is already proved for
all `s` by the original OpenAI PET proof. The canonical finite-word plan
has a theorem without that input hypothesis; see
[recurrence](nilpotent-recurrence/README.md). The actual weighted polynomial
shear group, dimension-independent nilpotence bound, measure preservation
and box total-variation estimate are in
[weighted shear laws](weighted-shear-box-laws/README.md); the genuine BCH
weighted realization is in
[native weighted actions](weighted-shear-native-actions/README.md).
The full uniform Alignment theorem remains open.

## Verification boundary

Each linked addition has focused build/source/axiom evidence and hashes.
No new axiom or competing proof dependency is used by these additions.
The original 3,059-file manifest hashes remain unchanged. These additions
are not yet part of the canonical `Hindman168.lean` or `Verification.lean`.
No full-project replay or independent replay of all imported kernel
artifacts is claimed. Uncommitted work and successful isolated checks are
not promoted here to completion of an open node.
