# Uniform selected Alignment is proved

`Hindman168.hasUniformSelectedPrincipalAlignment` proves the exact existing
`HasUniformSelectedPrincipalAlignment` definition with no hypotheses.

For every `n,r,s`, finite positive scale data `B,A`, the finite-scale closure
and a positive number `delta` are chosen BEFORE the master parameters,
ambient dimension, selected embedding, native model family, complexity and
positive threshold. The conclusion is the ordinary-filter liminf of the
literal `PrincipalSumAlignmentEvent` under `selectedPrincipalRawMass`.
The underlying full raw sample and ambient arithmetic scales are retained
throughout. The proof works in the declared arbitrary model universe.

## Actual construction

- Construct plans backwards along the fixed increasing pivot order, using
  the already proved original recurrence at step `s+1`. Every local plan
  is literally the plan used by the native coset mass theorem.
- Choose one clearing integer for all actual stage and final ratios.
  Choose `A` large enough for all actual route-factor scale lookups, then
  close it under the required final products. Colors are `Fin r`, so the
  scale set is not used circularly to select its own plan.
- Use the genuine full-raw local extension with multiplier `1/(3 Q_i^2)`.
  Deterministic first-success route selection partitions samples by the
  current scale state. Merging histories with equal states preserves the
  witnessed future-protected threshold path.
- Prove that each prefix event depends only on earlier raw coordinates;
  sum its finitely many state errors and apply the exact finite-pivot mass
  product. Unreachable states contribute empty events and zero error.
- Identify the resulting path with the existing native threshold event,
  apply the actual final-scale and denominator identities, and pass by the
  proved exact marginal law to the original selected alignment event.

The lower bound is the positive finite product `product_i 1/(3 Q_i^2)`;
none of its factors depends on models or thresholds. All conditional local
Haar, recurrence, asymptotic and probability assumptions have been discharged
in this endpoint.

## Main theorem boundary

`strongConjecture_of_native_inverse` now proves the unchanged original
`StrongConjecture` from ONLY

`forall t >= 2, HasNativePeriodicIntervalInverse (t-1) t`.

The higher-order inverse input is still unresolved in the main repository.
Therefore this batch does not yet give an unconditional `StrongConjecture`
proof, authorize publication, or justify submitting a prize claim.

## Verification

The 10 modules listed in `modules.json` were independently built with pinned
Lean 4.32.2 (6,929 jobs), and all 150 originating environment declarations
were audited with `lake env lean --trust=0`, including generated helpers.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. The log additionally
prints the exact uniform input definition and the two terminal theorem types
and axiom reports. Source hashes and original 3,059 snapshot checks are
recorded without changing canonical definitions or the historical manifest.
No independent replay of every imported kernel artifact is claimed here;
that is a separate final release verification requirement.
