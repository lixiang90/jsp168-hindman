from pathlib import Path
import re

prefix = 'round-original-linear-cube'
modules = [
 'NativeOriginalLinearOrbitPolynomial', 'NativeOriginalLinearOrbitAdapted',
 'AlignmentCanonicalPointOrbit', 'AlignmentOriginalJointLinearOrbit',
 'AlignmentOriginalJointCubeOrbit', 'AdaptedTaylorInitialZeros',
 'AdaptedTaylorBinomial', 'AdaptedTaylorRemoval', 'AdaptedTaylorRecursion',
 'AlignmentOriginalJointTaylorCoordinates']
components = [
 'The ACTUAL original heterogeneous joint point orbit is constructed in the literal finite product of original native array groups at the unchanged original step s. Every target retains its own tail product, exact integer residue correction, progression table, source and base array. The canonical native cube array is exactly the SAME point orbit at ell0 plus its original weighted increments; the integer origin Y cancels at the GROUP level.',
 'ALL-real native logarithmic polynomials for a genuine left-linear orbit are constructed from the original proved native product-log formula. Their aggregated coefficients lie in the ACTUAL ORIGINAL lower central Lie layers and their ordinary degree is at most the original step s. The parameter one is proved identical to the original lower central group/Lie series, and genuine real and signed-integer iterated differences use that SAME series. No loose degree bound or degree-dependent stretch replaces adaptation.',
 'Every common integer vertex profile across ALL original target components is exactly one state of the SAME heterogeneous joint point orbit. Arbitrary per-component profiles retain their actual point times. For one original target the quotient is literally the previously proved original native cube state, with no change to integer-slot/lattice readings. No other-marginal face invariance is inferred.',
 'The initial-zero Taylor layer lemma is proved for ANY antitone real vector filtration by quotient dual projections and genuine finite polynomial zero counting. An actual adapted polynomial vanishing at the first j integers has ALL-real values in layer j. This is an algebraic theorem, not a supplied Taylor representation or finite-difference oracle.',
 'Actual binomial correction and original native group product construct each ordered Taylor residual, preserving the SAME original lower central weights and adding one genuine initial integer zero. Natural recursion constructs every residual and ordered product. Original step s makes residual s+1 vanish at EVERY real input, giving the complete all-real ORDERED Taylor representation, actual coefficient membership in each original group layer, and actual nonnegative integer binomial powers. The construction also covers original step zero.',
 'The ordered Taylor representation and all actual group-layer coefficient memberships are instantiated by the ACTUAL original all-target joint linear orbit. Exact signed original integer inputs recover the genuine original joint state. Sequential smooth/equidistributed/periodic factorization is still unproved; Taylor coordinates alone do not assert coefficient irrationality, local Haar laws or final StrongConjecture.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
 'The ACTUAL original heterogeneous all-target joint linear orbit, canonical cube vertex identities, original lower central ALL-real coefficient/group-difference adaptation and original step-s complete ORDERED Taylor coordinates are now proved. '
 'Remaining: general rational filtered Taylor closure and genuine sequential smooth/equidistributed/periodic factorization with ONE rational filtration, strict finite descent, coefficient irrationality, sequence-selected period and bounded smooth-factor limits; local cube-Haar laws on every original dimension through s+1; sequence limit BEFORE relative-box-size limit, projected Haar face invariance and full-support coset symmetry; actual joint face lifts/full Alignment; separate arbitrary-input GTZ interval Gowers LINEAR nilsequence inverse at sufficient native step; final positive distinct rapidly separated SAME-color nonempty FS AND FP. '
 'Author checks are not independent kernel replay or external peer review. No explicit delta-power law or other-marginal invariance is claimed. The repaired slab estimate is not an unavoidable obstruction. Public repository/PR/prize milestone not reached.')
src = Path('round-native-complete-cube-probability-audit.py').read_text(encoding='utf-8')
src = src.replace('round-native-complete-cube-probability', prefix)
src = src.replace("OLD='round-native-cylinder-diagonal'", "OLD='round-native-complete-cube-probability'")
src = re.sub(r'^MODULES=.*$', 'MODULES='+repr(['Hindman168/'+m+'.lean' for m in modules]), src, flags=re.M)
src = re.sub(r'^COMPONENTS=.*$', 'COMPONENTS='+repr(components), src, flags=re.M)
src = re.sub(r'^REMAINING=.*$', 'REMAINING='+repr(remaining), src, flags=re.M)
src = src.replace("r'\\b(?:set_option|setOptions|instance|structure)\\b'",
                  "r'\\b(?:set_option|setOptions|structure)\\b'")
src = src.replace("  assert (Path('.lake/build/lib/lean')/Path(p).with_suffix('.olean')).stat()",
                  "  assert not re.search(r'^\\s*(?:(?:private|protected|noncomputable)\\s+)*instance\\b',helpers.lean_code(read(p)),re.M),p\n  assert (Path('.lake/build/lib/lean')/Path(p).with_suffix('.olean')).stat()")
Path(prefix+'-audit.py').write_text(src, encoding='utf-8')

review = '''JSP-000168 / Erdos #172 -- author mathematical review, 2026-10-14
Verdict: Partial overall coverage; PROGRESS. StrongConjecture UNPROVED.
Goal ACTIVE; no unavoidable obstruction established.
Author checks are not independent kernel replay or external peer review.

Primary source: OpenAI math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
08_alignment.tex 363--377 (actual original joint linear array orbit), and
07_cube_limits.tex 187--208, 246--258 (adaptation and ordered Taylor coordinates).
All six retained paper sections are compared to pinned Git objects.

1. Actual orbit. CanonicalPointExponent is the exact original integer quotient
tau*p/M plus the exact original integer residue correction. Canonical cube
group membership is already proved in the retained model-array constructor.
CubeBase/Vertex affine identities cancel Y before any quotient projection.
Different target components retain THEIR own tau and progression indicators.
All component equations come from the literal native product projection.
The empty finite family remains the actual trivial product.

2. Adaptation. The native product-log polynomial is used on singleton X*log(g)
and constant log(a); the true termwise original Lie weights are preserved.
Parameter ONE equals the actual lower central series, with paper indices
K_0=K_1=K. Aggregated coefficients have their original lower central membership.
Zero trimming removes ONLY zero vectors, preserving all actual values and
weighted coefficients. Original terminal layer s+1 forces degree at most s.
All-real group differences are derived by the previously proved actual native
weighted difference construction; signed-integer restriction is exact.
Neither the old loose model-log degree bound nor a larger stretch is used.

3. Cube identity. Common vertex profiles give one common joint point time.
Per-component profiles are represented by their own times in the same orbit.
Uniform target specialization is definitionally the ORIGINAL native empirical
cube quotient state. Arbitrary integer weights include every zero/one vertex,
with no restriction on original cube dimension. This algebra does NOT assert
the joint face invariance of other marginals.

4. Taylor layer argument. Project the vector log polynomial to the quotient
by F_j, then apply every algebraic scalar dual. Weighted coefficient membership
makes ALL scalar coefficients of degrees >=j zero. For j>0 the scalar degree
is at most j-1. Its j distinct values at 0,...,j-1 vanish; the genuine finite
root-count theorem forces it to be zero. Algebraic dual separation therefore
gives layer membership at EVERY real input. The j=0 Taylor step uses the
genuine weighted value in F_0, not a nonexistent positive root count.

5. Ordered construction. The correction at stage j is exp(-binom(b,j)*v_j),
where v_j is the actual current residual log at the actual integer j. Its
polynomial degree <=j and v_j lies in original layer j. Original product
weights prove adaptedness after correction; at m<j, binom(m,j)=0, and at
m=j it is one. Thus the next residual has j+1 initial integer zeros.
The recursion retains the exact ALL-real product identity; inverse cancellation
is proved in the actual group. The ordered product places each removed factor
on the RIGHT of the accumulated prefix, preserving the noncommutative order.
There is no commutation of Taylor factors.

6. Terminal step. Stage s+1 has s+1 genuine initial integer zeros and original
weighted coefficients. The layer argument and ACTUAL original nilpotence make
its log value zero at EVERY real input. The ordered reconstruction therefore
has no residual. This covers s=0, where the original data already force the
group to be trivial. Natural sample powers are actual choose(m,j) powers;
the full real identity and signed-integer original orbit identity do not rely
on extrapolating those natural choose values to negative integers.

7. Original instantiation. The genuine all-target joint source has the proved
original weighted log, so its ordered representation has exactly s+1 factors,
including the constant factor at index 0. Every actual coefficient lies in
the SAME original lower central group layer. All signed original orbit inputs
are recovered by the true native integer exponential identity.

8. Trust and boundaries. No new axiom, sorry, admit, native decision shortcut,
kernel bypass, heartbeat change or extra analytic production premise is used.
Development logs preserve the model/Lie-algebra type-matching diagnostics.
Typed equality transport fixes these without changing mathematics or toolchain.
Old proof source hashes and transitive selected axiom sets are compared by the
terminal audit. Standard axioms remain propext, Classical.choice, Quot.sound.

9. Remaining. This closes the ORIGINAL linear-adaptation interface and the
starting original lower-central ordered Taylor coordinates. It does not prove
the lemma's sequential finite rational filtration descent, simultaneous character
irrationality, rational periodic factors or convergent smooth factors. General
Taylor closure for descended rational filtrations still needs proof. The actual
local cube-Haar law, sequence-before-locality limit, marginal Haar/coset symmetry,
joint lifts, full Alignment, distinct GTZ Gowers correlation inverse and final
same-color positive distinct rapidly separated FS AND FP remain UNPROVED.
Publication is pending the user's stated completion-or-unavoidable-obstruction
milestone. No unavoidable obstruction or award eligibility is asserted.
'''
Path(prefix+'-mathematical-review.txt').write_text(review, encoding='utf-8')
print('Prepared author audit for '+str(len(modules))+' new modules.')
