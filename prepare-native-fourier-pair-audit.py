from pathlib import Path
import ast
import re

prefix = 'round-native-fourier-pair'
old = 'round-native-central-pullback'
modules = [
    'CentralSubgroupFactorMap', 'CentralSubgroupFactorFibers',
    'DiagonalCenterSubgroup', 'ContinuousConjugatePair',
    'CentralSubgroupFactorObservable', 'NativeFourierPairObservable',
    'NativeFourierPairInvariance', 'NativeFourierPairFactor',
    'RoughVectorMvPairPolynomial', 'NativeFourierPairPolynomial',
    'NativeFourierPairFactorCompact',
]
components = [
    'ACTUAL normal-subgroup quotient/image-lattice map on ORIGINAL nonnormal lattice cosets is constructed, surjective, invariant under original subgroup action and an OPEN quotient map. True continuous image of original compact cosets supplies actual factor compactness. Original lattice normality is never assumed.',
    'For an ACTUAL central subgroup N, genuine factor fibers equal ORIGINAL N-action orbits exactly, by original quotient equality and actual lattice representatives. No fiber-orbit equivalence is assumed.',
    'The ACTUAL diagonal of ORIGINAL center in G times G is constructed. Membership is exactly a pair (z,z) with z in original center. Its center inclusion and normality are PROVED. Original product coset equivalence is equivariant under ACTUAL diagonal action.',
    'Actual continuous conjugate pair F(q)*star(G(r)) has genuine uniform norm bound and joint continuous dependence on original continuous functions. An ACTUAL compact input family has compact paired image; not asserted spatially Lipschitz.',
    'Genuine continuous descent of ACTUAL central-subgroup-invariant original observables to actual quotient/image lattice retains ALL point values, has uniqueness and pointwise bounds. Actual generic hypotheses are later fully discharged for original Fourier pair, rather than assumed at native application.',
    'ACTUAL product coset projection into ORIGINAL specified metric factors is continuous using PROVED product-metric/original quotient topology equality. ACTUAL same-frequency original paired Fourier observable on original product lattice cosets is constructed with exact pointwise formula. Its functionspace dependence is continuous and image of ORIGINAL unit family is compact.',
    'ACTUAL original Fourier eigencharacters have modulus one, so phase and conjugate phase cancel EXACTLY in original paired observable. Genuine ORIGINAL diagonal center action invariance and ACTUAL diagonal subgroup invariance are PROVED for all frequencies, including nonzero. No derivative invariance premise.',
    'The ORIGINAL same-frequency paired Fourier observable genuinely descends to ACTUAL ORIGINAL diagonal-center group quotient/image lattice, with exact values on original product cosets and unique continuous descent. Actual factor is compact and projection open. This is actual factor coset geometry, not yet a fully constructed native filtered nilmanifold; closedness/rational lattice/compatible metric/induction complexity still need work.',
    'An ACTUAL product-model vector polynomial is constructed by true linear inclusions and addition. Original degree bounds and actual product-model evaluations are preserved.',
    'The ACTUAL shift-pair polynomial retains original degree and gives EXACTLY the ORIGINAL shifted and unshifted integer polynomial orbit under the TRUE product coset map. Actual factor observable evaluated on actual projected pair orbit is EXACT original same-frequency derivative value. For EVERY actual finite sample set, factor sample mean is EXACT original derivative average. Polynomial coefficients and shifts are unrestricted; no replacement samples.',
    'Descent of ACTUAL paired observables is contractive on uniform-norm differences, from actual factor-map surjectivity and exact values. This gives genuine continuous dependence on original F and ACTUAL COMPACT descended pair family for every fixed frequency. ORIGINAL unit family yields actual factor pointwise norm at most ONE. No spatial Lipschitz bound, canonical factor Haar agreement, nilpotency/dimension decrease or quantitative inverse is inferred.',
]
source = Path(old+'-audit.py').read_text(encoding='utf-8')
remaining = ast.literal_eval(re.search(r'^REMAINING = (.*)$', source, re.M).group(1))
start = 'NEXT genuine original nonzero-frequency derivative/product-group polynomial compatibility and quantitative Leibman induction, with explicit rational filtration and actual derivative-orbit geometry; no unproved child inverse or derivative interface may count as completion.'
replacement = ('Actual same-frequency Fourier pair observable is NOW constructed on ORIGINAL product lattice cosets, with genuine diagonal-center invariance and unique continuous descent to ACTUAL diagonal-center quotient/image lattice. Its actual shifted-pair polynomial preserves degree and gives SAME original shifted/unshifted integer orbit; actual factor sample mean equals original derivative average for EVERY finite sample set. Actual descended pair family is uniform-norm COMPACT and pointwise bounded by ONE for original unit inputs. This is NOT a quantitative inverse or a completed rational filtered nilmanifold: diagonal subgroup closedness/rational image lattice/compatible metric and actual filtered subgroup induction geometry still need to be constructed and verified. NEXT actual product/factor canonical Haar compatibility, actual diagonal quotient native/rational geometry and suitable fiber-product filtration, then genuine nonzero-frequency quantitative Leibman induction. Product/diagonal-center quotient does NOT automatically decrease nilpotency step or original dimension. Existing group-difference polynomial/iterated filtration facts remain proved and should be reused; no unproved inverse interface may count as completion.')
assert start in remaining
remaining = remaining.replace(start, replacement)
for name, value in [('PREFIX', prefix), ('OLD', old),
                    ('MODULES', ['Hindman168/'+m+'.lean' for m in modules]),
                    ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^'+name+r' = .*$', lambda _: name+' = '+repr(value), source, flags=re.M)
source = source.replace('Audit actual original character/coefficient pullback, canonical abelian root and genuine step-two zero-frequency inverse branch.',
    'Audit actual same-frequency pair derivative, diagonal-center descent, compact family and exact original shifted polynomial samples.')
source = source.replace('06_rough_progressions: ACTUAL original character/grid/polynomial coefficient pullback, canonical-Haar ABELIAN root inverse and GENUINE step-two ZERO-FREQUENCY branch; nonzero-frequency/general nonabelian quantitative Leibman/full prize theorem open',
    '06_rough_progressions: ACTUAL Fourier pair derivative and diagonal-center descent, compact bounded family and exact original shifted pair polynomial samples; rational filtered geometry/canonical pair-factor Haar/nonzero-frequency quantitative Leibman/full prize theorem open')
Path(prefix+'-audit.py').write_text(source, encoding='utf-8')
print('Prepared '+prefix+'-audit.py for '+str(len(modules))+' modules')
