from pathlib import Path
import ast
import re

prefix = 'round-native-child-regularity'
old = 'round-native-probability-uniqueness'
modules = [
    'NativeCentralChildZeroObservable', 'CompactLipschitzAlgebra',
    'CompactLipschitzApproximation', 'NativeCentralChildRegularFamily',
    'NativeCentralChildDiscrepancy', 'LinearDiscrepancyStability',
    'NativeCentralChildRegularDetection', 'BoundedLipschitzNormalization',
    'NativeCentralChildUnitDetection',
]
components = [
    'The SAME original descended zero observable is represented as a continuous function in the ACTUAL child specified metric, using its proved quotient topology equality. Pointwise values at the ACTUAL factor projection, subtraction and original uniform norm contraction are proved; no spatial Lipschitz bound is inferred from topology equality.',
    'Actual spatial Lipschitz complex functions form a star subalgebra on ANY compact metric space. Genuine bounded product estimates and complex conjugation prove closure; actual distance functions separate distinct points.',
    'Genuine Stone-Weierstrass gives uniform density of actual spatial Lipschitz functions on ANY compact metric space. A compact family admits ONE FIXED finite approximant list before all its members, with genuine shared positive amplitude and spatial Lipschitz bounds obtained from finite sums.',
    'The actual child zero-observable map is Lipschitz ONE in uniform FUNCTIONSPACE norms, not asserted spatially Lipschitz on child points. Its actual image of the original unit-observable family is compact in the child specified metric function space. All generic finite regular approximation hypotheses are discharged from this actual family.',
    'The actual original zero-projection finite discrepancy equals actual child-metric finite discrepancy with genuine child canonical Haar, SAME original sample set and ACTUAL factor images. No replacement samples, measure agreement assumption or unit spatial regularity premise.',
    'Actual complex linear discrepancies of norm at most TWO have uniform approximation error less than twice the uniform function error. Genuine triangle inequalities give positive approximant discrepancy detection.',
    'ONE FIXED finite bounded spatial-Lipschitz child family detects EVERY original unit-observable zero-mode discrepancy at least eta, retaining discrepancy greater than eta/2 on the SAME projected samples and actual child canonical Haar. Family and all bounds are fixed BEFORE original observables and arbitrary finite samples.',
    'Actual common positive scaling sends bounded spatial-Lipschitz continuous functions into the actual unit Lipschitz observable family. Exact linear discrepancy scaling and norm identity are proved; no original descended unit regularity is assumed.',
    'ONE FIXED finite ACTUAL UNIT child family and a FIXED POSITIVE threshold detect all original zero-mode discrepancies uniformly before arbitrary original samples and observables. All compactness, approximation, normalization and canonical Haar hypotheses are now discharged. The child orbit inverse itself and nonzero-frequency induction are still unproved.',
]
source = Path(old+'-audit.py').read_text(encoding='utf-8')
remaining = ast.literal_eval(re.search(r'^REMAINING = (.*)$', source, re.M).group(1))
start = 'NEXT transport actual compact zero-mode family to child specified compatible metric and provide actual compact-family regularity approximation/child inverse induction; pull child horizontal characters/coefficients/norm bounds back through actual original model projection.'
replacement = ('The actual child-metric zero-mode family now has genuine uniform compactness and spatial Lipschitz approximation, with one fixed finite ACTUAL UNIT child family and positive fixed discrepancy threshold before all original observables and finite sample sets. SAME actual projected samples and child canonical Haar are retained. No topology-to-Lipschitz inference or assumed descended spatial regularity remains in this step. NEXT prove actual child horizontal character/coefficient/operator bounds pullback through original model projection, and assemble child orbit inverse induction; the child orbit inverse is still unproved.')
assert start in remaining
remaining = remaining.replace(start, replacement)
for name, value in [('PREFIX', prefix), ('OLD', old),
                    ('MODULES', ['Hindman168/'+m+'.lean' for m in modules]),
                    ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^'+name+r' = .*$', lambda _: name+' = '+repr(value), source, flags=re.M)
source = source.replace('Audit genuine original nonnormal invariant probability uniqueness and original central-factor canonical Haar compatibility.',
    'Audit actual child-metric compact zero-mode regularity and fixed finite unit-family discrepancy detection.')
source = source.replace('06_rough_progressions: GENUINE original nonnormal invariant probability uniqueness, exact transversal normalization and ACTUAL original central-factor/child canonical Haar agreement; regularity/nonabelian quantitative Leibman/full prize theorem open',
    '06_rough_progressions: ACTUAL compatible-metric child zero-mode compact regularity, finite spatial Lipschitz approximation and genuine fixed unit-family discrepancy detection; child orbit inverse/nonzero-frequency quantitative Leibman/full prize theorem open')
Path(prefix+'-audit.py').write_text(source, encoding='utf-8')
print('Prepared '+prefix+'-audit.py for '+str(len(modules))+' modules')
