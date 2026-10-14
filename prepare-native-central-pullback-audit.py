from pathlib import Path
import ast
import re

prefix = 'round-native-central-pullback'
old = 'round-native-child-regularity'
modules = [
    'NativeCentralCharacterPullback', 'NativeCentralCharacterHorizontal',
    'NativeCentralCharacterGrid', 'RoughVectorMvProjectionNaturality',
    'NativeCentralPolynomialProjection', 'NativeCentralObstructionPullback',
    'NativeCentralZeroPolynomialDetection', 'NativeAbelianCanonicalHaar',
    'NativeAbelianCanonicalInverse', 'NativeTwoStepZeroInverse',
]
components = [
    'Actual child real functional is pulled back through the ORIGINAL center-model continuous linear projection. Genuine actual right section proves NONZERO pullback. Actual operator norm is bounded by child norm times original projection norm. Actual original logarithm-character equals actual child character on the genuine group quotient.',
    'Actual quotient group multiplication and original/child logarithm compatibility prove genuine additivity of the original pullback. Actual character linearization then proves it kills the ORIGINAL commutator layer. ACTUAL image-lattice membership proves ORIGINAL lattice integrality. No original horizontal or integrality premise is assumed for the pullback.',
    'An explicit fixed parent operator budget A*(1+norm(original projection)) is nonnegative, at least A, and bounds the actual pulled character norm. The now PROVED original horizontal/integer properties give membership in the ACTUAL ORIGINAL fixed finite horizontal grid.',
    'Actual scalar multivariate polynomial after actual linear projection E-to-F equals the original scalar polynomial under the composed functional, as COMPLETE POLYNOMIALS and EVERY coefficient, not merely equality on samples.',
    'Actual original exp/log polynomial orbit projects to the GENUINE CHILD exp/log polynomial orbit with SAME integer variables. Original polynomial degree is retained. Actual arbitrary original logarithmic-polynomial representations project correctly as well. Child scalar polynomial and all coefficients equal those of the actual original pulled character.',
    'Actual parameter-specialized spatial scalar polynomials retain exact equality under child projection/pullback. Actual weighted monomial coefficient obstructions pull back into the ORIGINAL fixed finite horizontal grid with an explicit FIXED operator/coefficient budget.',
    'Actual original zero-mode discrepancy on the GENUINE logarithmic-polynomial orbit is detected by ONE FIXED finite UNIT child list and positive fixed threshold on the ACTUAL PROJECTED POLYNOMIAL orbit, before all polynomials and finite sample sets. All orbit/degree/metric/Haar/regularity compatibility is discharged.',
    'Actual abelian torus-coordinate Haar probability equals GENUINE ORIGINAL canonical Haar after explicit transport along the PROVED equality of raw/metric Borel sigma-algebras. Actual probability and full original group invariance discharge the already proved NONNORMAL uniqueness theorem. All actual complex integrals coincide with original canonical Haar; no measure agreement premise.',
    'The GENUINE ABELIAN root inverse now uses ORIGINAL canonical Haar and the actual original logarithmic-polynomial orbit. Fixed constants precede all polynomial coefficients, positive cube lengths and unit observables. An actual nonzero original horizontal character is produced in the original finite grid with BOTH ordinary monomial and paper-binomial coefficient bounds. No inverse existence hypothesis is supplied.',
    'The ZERO-FREQUENCY inverse branch for ACTUAL step-at-most TWO native data is NOW genuinely completed: its actual child is abelian, the new PROVED canonical abelian inverse applies to the actual finite unit child detection, and genuine character/grid/scalar coefficient pullback gives ORIGINAL nonzero horizontal obstruction with BOTH monomial and paper-binomial bounds. Constants depend only on fixed native data, input dimension, degree and accuracy, before all coefficients and N. Premise is explicitly a zero-projection discrepancy; NONZERO-frequency branch and full step-two/nonabelian inverse remain unproved.',
]
source = Path(old+'-audit.py').read_text(encoding='utf-8')
remaining = ast.literal_eval(re.search(r'^REMAINING = (.*)$', source, re.M).group(1))
start = 'NEXT prove actual child horizontal character/coefficient/operator bounds pullback through original model projection, and assemble child orbit inverse induction; the child orbit inverse is still unproved.'
replacement = ('Actual child character pullback NOW genuinely preserves nonzero/horizontal/original lattice-integral properties with explicit operator bounds and ORIGINAL finite-grid membership. Actual polynomial orbit/degree/log representations and COMPLETE scalar polynomial/monomial/spatial-specialization coefficients are retained. ABELIAN root inverse NOW uses genuine ORIGINAL canonical Haar with proved measure/integral agreement. The actual step-at-most TWO ZERO-FREQUENCY inverse branch is NOW proved, producing a genuine ORIGINAL nonzero finite-grid horizontal character with BOTH monomial and paper-binomial bounds from the PROVED actual abelian child inverse. This is NOT a full step-two inverse: NONZERO central-frequency discrepancies and general child/nonabelian orbit inverse still remain open. NEXT genuine original nonzero-frequency derivative/product-group polynomial compatibility and quantitative Leibman induction, with explicit rational filtration and actual derivative-orbit geometry; no unproved child inverse or derivative interface may count as completion.')
assert start in remaining
remaining = remaining.replace(start, replacement)
remaining = remaining.replace('Canonical-measure abelian root assembly, generic finite-index rough API,',
    'Canonical-measure abelian root inverse is now proved. Generic finite-index rough API,')
for name, value in [('PREFIX', prefix), ('OLD', old),
                    ('MODULES', ['Hindman168/'+m+'.lean' for m in modules]),
                    ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^'+name+r' = .*$', lambda _: name+' = '+repr(value), source, flags=re.M)
source = source.replace('Audit actual child-metric compact zero-mode regularity and fixed finite unit-family discrepancy detection.',
    'Audit actual original character/coefficient pullback, canonical abelian root and genuine step-two zero-frequency inverse branch.')
source = source.replace('06_rough_progressions: ACTUAL compatible-metric child zero-mode compact regularity, finite spatial Lipschitz approximation and genuine fixed unit-family discrepancy detection; child orbit inverse/nonzero-frequency quantitative Leibman/full prize theorem open',
    '06_rough_progressions: ACTUAL original character/grid/polynomial coefficient pullback, canonical-Haar ABELIAN root inverse and GENUINE step-two ZERO-FREQUENCY branch; nonzero-frequency/general nonabelian quantitative Leibman/full prize theorem open')
Path(prefix+'-audit.py').write_text(source, encoding='utf-8')
print('Prepared '+prefix+'-audit.py for '+str(len(modules))+' modules')
