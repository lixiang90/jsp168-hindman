from pathlib import Path
import re

prefix = 'round-rough-freezing-affine-obstruction'
stems = ['RoughNativePartitionFreezing', 'RoughMvAffineMonomialCoefficient',
    'RoughMvAffineCoefficient', 'RoughAffineBinomialCoefficient',
    'RoughFixedAffineCoefficient', 'RoughActualAffineObstructionModels']
modules = ['Hindman168/' + s + '.lean' for s in stems]
components = [
    'RoughNativePartitionFreezing chooses one positive natural balanced-partition count from the actual native action freezing modulus before all progression indices, original signed box endpoints, coefficient models, group maps and Lipschitz tests. Every actual half-open selected piece freezes its left factor at its original lower anchor with test error strictly below the prescribed tolerance.',
    'RoughMvAffineMonomialCoefficient constructs the exact coordinatewise binomial expansion over an actual finite Cartesian product of exponent ranges. It proves the actual coefficient of every affine substituted monomial product over an arbitrary commutative semiring, including exponents outside the original coordinate range.',
    'RoughMvAffineCoefficient proves the actual affine substituted monomial coefficient and the exact finite original-support sum formula for every multivariate polynomial over a commutative semiring.',
    'RoughAffineBinomialCoefficient separates the uniform scaling factor p to the total target degree, identifies the real coefficient weight with the original integer roughBinomialWeight, and proves the actual coefficient formula for finite function-indexed scalar polynomials. Positive-degree coefficients do not receive a spatial constant-term contribution.',
    'RoughFixedAffineCoefficient identifies this formula for the exact roughSpatialFixedPolynomial and roughFiniteMultiindices interfaces already used by the joint horizontal character model and triangular interpolation modules.',
    'RoughActualAffineObstructionModels applies the earlier uniform paper-growth triangular interpolation to bounds on actual affine substituted spatial polynomial coefficients. It constructs the rational integer coefficient models from those actual coefficient obstructions, preserving every original smooth-step, roughness, degree, scale and progression hypothesis.',
]
remaining = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'The actual native balanced-piece freezing error, affine substituted-coefficient formula and its direct connection to uniform rational coefficient-model extraction are now proved, along with previously verified packaged kernel logarithms, exact sampling transport, model cosets and induced-test interfaces. '
    'Assemble actual label-indexed native approximants and fixed finite quotient choices along unbounded bad progression lengths. '
    'The full quantitative Leibman obstruction and its uniform finite character list, corrected arbitrary-box comparison, stretched-filtration prerequisites, finite density extraction, dimension induction and uniform rough-step theorem remain open. '
    'Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs, and final ordered positive rapidly separated monochromatic extraction remains open. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
review = [
    'The natural partition count is chosen from the uniform continuous native action modulus and then fixed before all varying proof data. Signed original endpoint bounds and actual balanced-cut containment bound both sample and anchor; the closed upper bound used in the oscillation estimate is derived from actual half-open sample membership.',
    'Native freezing keeps the original ordered factorization at the exact sample. Only the scalar left factor is replaced by its actual lower-anchor value, and the original right model factor remains on the right. No coefficient bound for the new kernel map or analytic derivative assumption is introduced.',
    'The coefficient proof expands each coordinate power by the binomial theorem, multiplies the finite sums using the actual Cartesian exponent box, and extracts the unique original monomial exponent. Coefficients outside that box vanish through Nat.choose_eq_zero_of_lt, not an assumed support formula.',
    'The generic coefficient theorem expands the original polynomial by its actual finite support. It does not assume that an arbitrary named coefficient list equals the polynomial coefficients or discard nonzero lower terms.',
    'Uniform natural scaling contributes exactly p to the sum of target exponents. The remaining coefficient is the cast of the original integer triangular binomial weight; actual function and finitely-supported exponent interfaces are identified explicitly.',
    'The spatially constant contribution vanishes only under the explicit positive spatial degree hypothesis. The original constant coefficient polynomial remains arbitrary and is not assumed rational or integral at this stage.',
    'The final extraction theorem replaces the earlier stated binomial-expression bound by a bound on the actual substituted-polynomial coefficient. Quantitative Leibman still has to supply that bound, a nonzero character from one fixed finite list, and the associated uniform constants. No quantitative equidistribution theorem is assumed proved by this algebraic bridge.',
    'All retained proof sources and previous axiom sets remain unchanged. New proofs contain no sorry, axioms, unsafe computation or tactic-limit increases. Author-side verification does not prove StrongConjecture or constitute independent kernel replay.',
]
source = Path('round-rough-packaged-descent-audit.py').read_text(encoding='utf-8')
for name, value in {'PREFIX': prefix, 'OLD': 'round-rough-packaged-descent',
        'MODULES': modules, 'COMPONENTS': components, 'REMAINING': remaining}.items():
    source, count = re.subn('^' + name + r'\s*=.*$', lambda _: name + ' = ' + repr(value), source, flags=re.M)
    assert count == 1, name
a = source.index('application_review=COMPONENTS+')
b = source.index('verified=summary', a)
source = source[:a] + 'application_review=COMPONENTS+' + repr(review) + '+[REMAINING],\n        ' + source[b:]
source = re.sub("reference_scope='[^']*'", "reference_scope='06_rough_progressions actual balanced-piece native freezing and affine substituted coefficient obstruction models'", source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print('Prepared audit for', len(modules), 'modules.')
