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
actual coset covers. See [zero extension](interval-zero-extension/README.md),
[model signatures](bounded-model-codes/README.md), and
[cover transport](coset-cover-transport/README.md).

Still needed: complete checked integration of the exact normalized
interval-to-upstream Gowers adapter and compatible upstream GTZ dependency
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

The remaining geometric and realization chain is:

- Complete and verify one full heterogeneous joint source extraction with
  all target marginal symmetries on the SAME sample/subsequence,
  filtration, period, rational representatives, and smooth curve.
- Identify the actual projected cube orbits with the necessary image
  filtration and quotient geometry, keeping complete marginal cubes and
  binary vertex projections distinct; do not substitute independently
  selected target Haar laws.
- Finish the native Proposition 7.5 covering/lifting and derive the actual
  image-filtration graded identities and adapted coordinates. Given these
  geometric inputs, actual BCH affine maps and filtered lifts are now proved
  to be strict weighted shears.
- Connect those transformations to the common Haar weak limit and finish
  the finite integer realization needed for the uniform mass bound. The
  exact `HasAlignmentMonomialRecurrence s` input is now proved for every `s`
  by the original OpenAI PET proof, and the canonical finite-word plan has
  a theorem without that input hypothesis; see [recurrence](nilpotent-recurrence/README.md).
- Prove the actual native-model event adapter to the new concrete
  `PrincipalSumAlignmentEvent` used by the final deduction. Its late-stage
  ratio identity is proved, but this native-event implication is still open.

The actual weighted polynomial shear group, dimension-independent
nilpotence bound, measure preservation, and weighted-box total-variation
limit are verified in [weighted-shear-box-laws](weighted-shear-box-laws/README.md).
The actual native BCH weighted realization under explicit geometric inputs
is verified in [native weighted shears](weighted-shear-native-actions/README.md).
The common Haar weak-limit identification and full Alignment theorem remain open.

## Verification boundary

Each linked addition has focused build/source/axiom evidence and hashes.
No new axiom or competing proof dependency is used by these additions.
The original 3,059-file manifest hashes remain unchanged. These additions
are not yet part of the canonical `Hindman168.lean` or `Verification.lean`.
No full-project replay or independent replay of all imported kernel
artifacts is claimed. Uncommitted work and successful isolated checks are
not promoted here to completion of an open node.
