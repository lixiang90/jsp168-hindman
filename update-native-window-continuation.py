from pathlib import Path
import json

manifest=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert manifest['build_log']=='round-alignment-native-window-build.txt'
checks=json.loads(Path('round-alignment-native-window-checks.json').read_text(encoding='utf-8'))
assert not checks['full_target_proved'] and checks['standard_axioms_only']
note='''JSP-000168 / Erdos #172. Continuation after round-alignment-native-window.
Goal ACTIVE; StrongConjecture UNPROVED; no unavoidable obstruction established.
Authoritative terminal record: verification-manifest.json / last_round.
Author checking is not independent kernel replay or external peer review.

COMPLETED NATIVE ROUGH ROUTE:
Original complex non-strict rough exceptional-proportion comparison is proved,
including finite dense AP input and native finite-rank no-long-bad induction.
Common finite-native-family budgets precede all raw source/sampling data.
Literal native x=a+q*y source substitution preserves the removed parameter;
q and a are fixed while t varies. Nested original q/q*t sampling, complex
discrepancy and compatible residue identities need NO gcd(q,t).
Arbitrary real boxes are handled by exact ceil geometry and actual simultaneous
coarse/fine nonemptiness derived from growth. Comparison holds on ANY actual
cofinal sieve-width sequence, including repeats/oscillation, with actual
smoothness and primorial conditions at W(k), never the sample index k.
Bounded varying normalized scales retain every actual endpoint/observable/
compatible residue/discrepancy witness. Positive dyadic retained products
derive a FIXED range factor 2^card independent of actual tuples/models.

ACTUAL CONDITIONAL-PROBABILITY CONNECTION:
ConditionalProductFiberComparison proves exact uniform count fractions,
original product pivot-coordinate Fubini with support-restricted fibers,
finite coordinate unions and actual positive-event conditioning domination.
Conditioned factors are never assumed independent.
AlignmentPosteriorFiberComparison applies the proved ACTUAL short-exposure
posterior domination with constant 3*2^T.card before all events/models.
Raw positive anchors ensure genuine nonempty factor windows and total-one laws.
Native fiber caps must still be instantiated on actual source/event packets.

ACTUAL MASTER WINDOW CAPS, NOW PROVED:
PowerDominationRealRatios derives every positive REAL exponent paper ratio
from genuine natural-power little-o and positive scale denominators.
AlignmentNativeReferenceGrowth supplies actual master reference-scale ratios
and typical factor-scale divergence from MasterParameterConditions.
AlignmentNativeWindowSampling proves exact binary-window/rough-dyadic-set and
uniform-law equality, including half-open endpoints and actual representatives.
It derives smoothness, primorial divisibility and residue rough units from the
ACTUAL supported master law; retained q need not be coprime to removed t.
AlignmentNativeWindowUniform obtains the reference analytic budget from the
PROVED finite-native-family theorem. Growth, arithmetic, density and positive
normalization are discharged rather than assumed.
ActualSelectorUniformity and AlignmentNativeWindowAllAnchors promote this to
ONE eventual cutoff before ALL supported typical anchors, retained subsets
and tail directions. Positive actual typical-event mass supplies real valid
anchors at all large widths. Defaults are confined to initial invalid widths,
with no claimed source/model/analytic truth. Empty tails remain vacuous.
AlignmentNativeWindowCap explicitly records the legitimate raw polynomial/log
packet and bounded normalized-geometry inputs; the cap itself is PROVED,
not an assumed analytic oracle.

NEXT MAIN ROUTE:
1. Construct and instantiate actual native Alignment source/fiber packets.
   Useful EXISTING audited source modules:
   AlignmentNativeExposedJointLog: genuine scalar exposed joint log polynomial,
   fixed degree ((s*s+1)^(s+1))*max(1,T.card), frozen exposure and actual cube
   evaluation into alignmentNativeCoefficientLog.
   RoughVectorMvCoordinates: actual finite basis/list vector polynomial assembly,
   degree and evaluation. Convert the actual joint scalar coordinates to the
   native joint Lie model, not to an artificial nilmanifold with analytic fields.
   AlignmentNativeJointNilmanifold: actual finite joint native nilmanifold.
   AlignmentMasterRetainedCRT: genuine retained representative bounds/classes
   AND retained-product/representative update invariance when removed j is not
   in U. These already prove the required independence algebra; use them.
   AlignmentPermittedRetainedGeometry: actual transformed box/endpoints bounds.
   NativeResidualSource: literal all-real spatial composition and degree/log
   identity. Do not replace actual sampling by a supplied coprime CRT premise.
   Freeze exposure, other factors and U before removed t. Preserve the actual
   quotient observables, native joint Lie coordinates and fixed degree bound.
   All-real polynomial extension must match the ACTUAL valid sampled arrays;
   source values off the sample cannot substitute for this identity.
   Derive actual bounded scale ranges with ResidualScaleVariation and genuine
   posterior dyadic supports. Then use the all-anchor native window cap and
   actual posterior Fubini union theorem. Source/event inclusion, observables
   and complete cube/Alignment synthesis still need proofs.

2. Separate GTZ interval Gowers correlation inverse remains unproved.
   NativePeriodicIntervalInverseThreshold defines HasNativePeriodicIntervalInverse,
   requiring arbitrary bounded periodic inputs and LINEAR nilsequence correlation
   with a fixed finite native list/Lipschitz/positive correlation before q,K,v.
   Completed native equidistribution inverse does NOT discharge this. Existing
   master inverse projection and short-cube steps remain conditional on this
   genuine proposition. A missing library theorem is not an unavoidable block.
   Preserve full quantifiers and actual K=0/d=0 semantics.

3. Final full cube/Alignment and positive distinct rapidly separated FS/FP.
   StrongConjecture is unchanged. One common color must cover every nonempty
   sum AND product, for arbitrary finite coloring and witness length.
   Fixed-data existential constants do not certify explicit delta-power laws.

DEPENDENCIES AND CHECKING:
Main pins unchanged: Lean 4.32.2 and mathlib
905b95818eb32af7874a58b427f50c1711a5e96c.
Nine attributed PNT+ modules retained. The 42-module minimal attributed finite
Szemeredi closure is certified under these pins, with source attribution,
Apache-2.0 license and all compatibility/provenance files preserved.
The separate 4137-module full dense-progression archive remains UNVERIFIED
and not imported. Do not confuse it with the certified minimal closure.
Keep all registered source hashes and old axiom sets exact; add new modules,
root imports and registry only. No sorry/admit/custom axiom/native_decide/
unsafe/option/instance bypass. Explicit autoImplicit=false checks must have
EMPTY logs. Run complete build, expanded selected transitive standard-only
axiom audit and actual pinned paper-source comparison before registration.

PUBLICATION:
Only completed formalization or a genuinely established unavoidable obstruction
reaches the user's public-repository/PR/prize milestone. Neither has occurred.
Repaired source slab estimate, compiler APIs or absent library imports are not
obstruction certificates. Preserve paper/dependency/solver authorship accurately.

LATEST TERMINAL AUDIT, 2026-10-13: round-alignment-native-window.
'''
note+=json.dumps(checks,indent=2)+'\n'
note+='This goal turn added 19 modules, 55 theorems and 10 definitions across five\nterminal author audit rounds. No audit/compiler process is still active.\nStrongConjecture UNPROVED; goal ACTIVE; no unavoidable obstruction established.\n'
Path('NATIVE-ORIGINAL-ROUGH-PROPORTION-CONTINUATION.txt').write_text(note,encoding='utf-8')
print('Updated continuation after terminal recorded audit.')
