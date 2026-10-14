from pathlib import Path
import re

prefix = 'round-rough-residue-transport'
stems = ['RoughResidueCoordinateEndpoints', 'RoughResidueCoordinateGeometry',
    'RoughResidueCoordinateStep', 'RoughResidueBoxTransport', 'RoughResidueBoxSampling',
    'RoughResidueScaleGrowth', 'RoughResidueBoxGeometry']
modules = ['Hindman168/' + s + '.lean' for s in stems]
components = [
    'RoughResidueCoordinateEndpoints constructs actual integer coordinates of the first residue point for arbitrary signed half-open interval endpoints. It proves endpoint reconstruction, bounds, monotonicity, and the exact affine interval image.',
    'RoughResidueCoordinateGeometry proves that K times the transformed side differs from the original side by less than K. Original sides at least 2K give uniform transformed side bounds, and original sample positions give the required rescaled coordinate bound.',
    'RoughResidueCoordinateStep uses coprimality to identify the original step-t condition under x=u+Ky with one fixed residue condition modulo t on y. Its interval image is exactly the original step-t and step-K intersection.',
    'RoughResidueBoxTransport proves the coordinatewise finite Cartesian-product image identity, injectivity, and the actual unrestricted and step-t box images under the affine map.',
    'RoughResidueBoxSampling proves exact pushforward equality of the two actual uniform finite laws. The new step residue is chosen before every test function, and discrepancy is preserved exactly for every real test.',
    'RoughResidueScaleGrowth proves that fixed positive K preserves PowerDominates and every paper power-ratio divergence under Z to Z/K. It also supplies eventual rescaled scale larger than one.',
    'RoughResidueBoxGeometry proves uniform side bounds at scale Z/K and bounded transformed sample positions from the original box hypotheses.',
]
remaining = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'The bounded geometric partition, actual original-law piece selection, smaller native kernel nilmanifold, actual native logarithm transfer, and exact x=u+Ky conditional sampling transport with comparable box bounds and scale growth are now proved. '
    'Specialize native log transfer to the actual assembled kernel map and affine spatial substitution, and connect native freezing and finite-residue induced-test approximants to the constructed labels. '
    'Quantitative Leibman obstruction and its uniform finite character list, affine substituted-coefficient identity, corrected box comparison, stretched filtration, finite density extraction, dimension induction and uniform rough-step comparison remain open. '
    'Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs, and final ordered positive rapidly separated monochromatic extraction remains open. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
review = [
    'The affine change uses signed integer endpoints, not a truncation valid only for positive endpoints. Endpoint error is strictly less than K, and the lower bound is applied only when the original side is at least 2K.',
    'Coprimality is used for step-t transport, while positive K is used for injectivity and monotone interval transport. The same transformed residue works for all test functions and is independent of their values.',
    'Both uniform laws are transported exactly, including empty finite supports as zero masses. Separate earlier large-scale thresholds provide nonemptiness when probability laws are needed; no empty-support probability claim is introduced.',
    'Finite image and predicate equalities are proved extensionally to handle abstract versus concrete Lean decidability instances. This affects proof elaboration only and introduces no new mathematical hypothesis, axiom, or tactic limit.',
    'The new spatial scale Z/K retains every super-polynomial growth condition for fixed positive K. Fixed constants in side and position bounds do not depend on t, S, Z or a selected test.',
    'Actual transformed samples are bounded from membership in the original signed box. The upper endpoint is half-open and is handled using its strict inequality, without shifting or replacing the finite sampling support.',
    'All retained sources and previous transitive axiom sets are checked unchanged. Author-side checking does not prove StrongConjecture or the remaining existence inputs.',
]
source = Path('round-rough-native-log-transfer-audit.py').read_text(encoding='utf-8')
for name, value in {'PREFIX': prefix, 'OLD': 'round-rough-native-log-transfer',
        'MODULES': modules, 'COMPONENTS': components, 'REMAINING': remaining}.items():
    source, count = re.subn('^' + name + r'\s*=.*$', lambda _: name + ' = ' + repr(value), source, flags=re.M)
    assert count == 1, name
a = source.index('application_review=COMPONENTS+')
b = source.index('verified=summary', a)
source = source[:a] + 'application_review=COMPONENTS+' + repr(review) + '+[REMAINING],\n        ' + source[b:]
source = re.sub("reference_scope='[^']*'", "reference_scope='06_rough_progressions exact residue-coordinate box sampling transport and rescaled geometry'", source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print('Prepared audit for', len(modules), 'modules.')
