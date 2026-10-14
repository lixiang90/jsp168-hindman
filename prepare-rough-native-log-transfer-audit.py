from pathlib import Path
import re

prefix = 'round-rough-native-log-transfer'
stems = ['NativeLieSubalgebraNativeCoordinates', 'RoughVectorMvLinearMap',
    'RoughNativeSubgroupLogPolynomial', 'RoughNativeNilmanifoldLogTransfer']
modules = ['Hindman168/' + s + '.lean' for s in stems]
components = [
    'NativeLieSubalgebraNativeCoordinates proves that the actual smooth subgroup inclusion has differential at identity equal to its real model-subspace inclusion. Native exponential naturality then identifies the subgroup native exponential with the original exponential restricted to the model subspace. The genuine subgroup native logarithm is exactly the original ambient native logarithm with its proved subspace membership.',
    'RoughVectorMvLinearMap constructs the actual image of an arbitrary finite vector multivariate polynomial under a real linear map. Evaluation commutes with the map, and the uniform total-degree bound is preserved without any coordinate or coefficient bound.',
    'RoughNativeSubgroupLogPolynomial applies the constructed finite-dimensional continuous linear retraction to an actual ambient joint logarithmic polynomial. For every real parameter point of the actual subgroup-valued map, its evaluation equals the genuine subgroup native logarithm. Every real linear scalar coordinate is represented by an actual multivariate polynomial with the original total-degree bound.',
    'RoughNativeNilmanifoldLogTransfer applies this constructed coordinate transfer to the exact NativeNilmanifoldData of the previous rational subgroup/conjugated lattice constructor. It produces an actual vector polynomial and all scalar coordinate polynomials for the newly packaged group native logarithm, retaining the degree and all-real-parameter quantifier order.',
]
remaining = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'The bounded geometric subbox/residue partition, uniform thresholds, original weight and freezing/approximation losses, smaller native character-kernel nilmanifold with strict dimension decrease, and actual ambient-to-subgroup native logarithmic polynomial transfer are now proved. '
    'Apply native freezing and the uniform finite-residue induced-test approximants to the constructed piece labels; specialize the new log-transfer theorem to the actual assembled kernel map and affine spatial substitution. '
    'Prove the actual x=u+Ky conditional sampling transport and comparable transformed-box bounds, preserving uniform constants. '
    'The quantitative Leibman obstruction, affine substituted-polynomial coefficient identity, corrected box comparison, stretched-filtration prerequisites, finite density extraction, dimension induction and uniform rough-step comparison remain open. '
    'Package finite native readings and connect conditional face laws. Buffered short-bin geometry, prior-event positive probability, extra-conditioning posterior control, quantitative native smooth-observable bounds, conditional face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
review = [
    'The previous ambient logarithmic polynomial alone did not prove polynomiality in the newly packaged native subgroup model. These theorems discharge that coordinate obligation by identifying actual native exponential/logarithm via the actual subgroup inclusion differential.',
    'The inclusion differential is computed by actual manifold chain rules at zero on the restricted original exponential. Its subgroup singleton chart has identity derivative, while the original native exponential derivative at zero is identity. No replacement group exponential or unspecified chart conversion is assumed.',
    'The native subgroup Lie structure, chart, topology, rational scalar action, lattice and metric are exactly those constructed in the previous checked native nilmanifold package. Structural field identities are used by definitional reduction in the final native data wrapper.',
    'The actual ambient vector polynomial is mapped through a constructed continuous linear left inverse of the model subspace inclusion. Its vectors need not individually lie in the subspace. Actual all-real-parameter subgroup membership ensures the total evaluation lies in that subspace, and the proved retraction identity identifies it with the actual new native logarithm.',
    'The multivariate polynomial total-degree bound does not increase under linear retraction or scalar projection. Coefficients and basis norms remain unrestricted, as required by the bad-progression dimension induction. This is polynomiality in all real parameters, not just original integer samples.',
    'The new wrappers require an actual subgroup-valued map and its actual ambient vector polynomial. Earlier assembled kernel maps supply the corresponding ingredients, but their concrete specialization, x=u+Ky sample transport and uniform dimension-induction theorem remain explicit future work.',
    'One declaration originally emitted unused-section-instance warnings. Its theorem assumptions were narrowed with explicit omit declarations and the final focused runs/full build are warning-free. No tactic limit increase or additional logical axiom was introduced.',
    'All retained sources and previous transitive axiom sets remain unchanged. This author-side verification does not constitute independent kernel replay or prove the remaining existence inputs or StrongConjecture.',
]
source = Path('round-rough-geometric-descent-audit.py').read_text(encoding='utf-8')
for name, value in {'PREFIX': prefix, 'OLD': 'round-rough-geometric-descent',
        'MODULES': modules, 'COMPONENTS': components, 'REMAINING': remaining}.items():
    source, count = re.subn('^' + name + r'\s*=.*$', lambda _: name + ' = ' + repr(value), source, flags=re.M)
    assert count == 1, name
a = source.index('application_review=COMPONENTS+')
b = source.index('verified=summary', a)
source = source[:a] + 'application_review=COMPONENTS+' + repr(review) + '+[REMAINING],\n        ' + source[b:]
source = re.sub("reference_scope='[^']*'", "reference_scope='06_rough_progressions actual native subgroup log polynomial coordinates for character-kernel dimension descent'", source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print('Prepared audit for', len(modules), 'modules.')
