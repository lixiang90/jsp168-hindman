from pathlib import Path
import re

prefix = 'round-rough-slow-freezing'
modules = [
    'Hindman168/RoughMonomialOscillation.lean',
    'Hindman168/RoughScaledMonomialOscillation.lean',
    'Hindman168/RoughSlowPolynomialOscillation.lean',
    'Hindman168/RoughJointSlowOscillation.lean',
    'Hindman168/RoughCompactParameterFreezing.lean',
    'Hindman168/RoughNativeActionFreezing.lean',
    'Hindman168/RoughNativeModelFreezing.lean',
    'Hindman168/RoughNativeFrozenFactorization.lean',
    'Hindman168/RoughFrozenDiscrepancy.lean',
    'Hindman168/RoughConvexPieceSelection.lean',
]
components = [
    'RoughMonomialOscillation proves actual real power and finite monomial product oscillation bounds by finite algebraic telescoping, with uniform constants depending on the degree and a fixed normalized box radius.',
    'RoughScaledMonomialOscillation proves exact rescaling of actual monomial evaluation and combines coefficient decay with the normalized coordinate oscillation. On coordinates bounded by C*Z and coordinate differences at most delta*Z, the monomial change is bounded by degree*A*delta*C^degree.',
    'RoughSlowPolynomialOscillation cancels the actual constant coefficient and sums the actual monomial oscillation bounds. The whole slow polynomial changes by at most card(s)*d*A*C^d*delta, uniformly in Z and coefficient sizes.',
    'RoughJointSlowOscillation transfers that bound to the actual assembled joint slow polynomial at every original progression index, for arbitrary real spatial inputs.',
    'RoughCompactParameterFreezing constructs a uniform parameter modulus for a jointly continuous map on a compact strip. It obtains one positive scalar threshold before all Lipschitz test functions and points, with test error below any prescribed epsilon.',
    'RoughNativeActionFreezing proves joint continuity of the original exponential scalar action on the specified metric quotient by transporting both domain and target topologies through the proved compatible metric equality. It obtains uniform original nilmanifold test freezing.',
    'RoughNativeModelFreezing combines actual joint slow polynomial value and oscillation bounds with native test freezing. The positive subbox scale is chosen before every progression length, coefficient model, index, scale, observable and quotient point.',
    'RoughNativeFrozenFactorization specializes native freezing to the actual original ordered factorization g=exp(aV)*Q*exp(mV). It proves the frozen original quotient test error for the exact kernel factor, preserving multiplication order without a commutation assumption.',
    'RoughFrozenDiscrepancy proves that freezing with error epsilon under each of two actual finite probability laws decreases their discrepancy by at most 2*epsilon, with bounds needed only on the original supports.',
    'RoughConvexPieceSelection proves that after reweighting a convex combination by total absolute weight error, one positive-weight piece retains any discrepancy threshold strictly below the original discrepancy minus B times that weight error. No division by the number of pieces occurs.',
]
remaining = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'Actual slow-polynomial oscillation and original nilmanifold test freezing are now proved with one threshold preceding all varying progression and observable data. '
    'Freezing discrepancy loss and convex selection after bounded weight replacement are proved. '
    'These use a uniform continuity modulus for the specified compatible metric, not an unproved linear action bound. '
    'Uniform quantitative Lipschitz induced-observable bounds and exact finite residue sampling weights remain open. '
    'Actual scalar model assembly, integer spatial realization, original residue cosets, native joint kernel polynomiality, conjugated lattice compactness, joint orbit-map smoothness and affine spatial substitution were retained. '
    'The quantitative Leibman obstruction, affine substituted-polynomial coefficient identity, corrected box comparison, stretched-filtration prerequisites, finite density extraction, dimension induction and uniform rough-step comparison remain open. '
    'Package finite native readings and connect conditional face laws. Buffered short-bin geometry, prior-event positive probability, extra-conditioning posterior control, quantitative native smooth-observable bounds, conditional face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
source = Path('round-rough-model-assembly-audit.py').read_text(encoding='utf-8')
for name, value in {'PREFIX': prefix, 'OLD': 'round-rough-model-assembly',
                    'MODULES': modules, 'COMPONENTS': components, 'REMAINING': remaining}.items():
    source, count = re.subn('^' + name + r'\s*=.*$', lambda _: name + ' = ' + repr(value), source, flags=re.M)
    assert count == 1, name
a = source.index('application_review=COMPONENTS+')
b = source.index('verified=summary', a)
review = [
    'Section 06 freezes the left factor on a subbox. The actual scalar error polynomial has oscillation at most N*d*A*C^d*delta when coordinate variation is at most delta*Z. The power/product proof is direct algebra and does not mistake algebraic pderiv estimates for an analytic derivative theorem.',
    'The normalization identity is proved for the actual monomial evaluations. Coefficient decay cancels Z^degree exactly, while normalized coordinates and their changes are bounded by C and delta. The constant term cancels without any magnitude assumption on that constant.',
    'Original real sample indices z<H and arbitrary real spatial inputs are retained. The model freezing threshold is chosen before H, q, scale Z, coefficients, model polynomials, sample index, Lipschitz observable and quotient point. It depends only on fixed native data, V, support, degree, A,C,L and epsilon.',
    'NativeNilmanifoldData supplies an arbitrary compatible metric. A smooth map need not be Lipschitz in such a metric. The proof instead establishes actual action continuity in this metric and uses compactness to obtain the uniform modulus needed to select subboxes for a fixed target error. This proves the required freezing error, not a linear C2*delta estimate for all delta.',
    'Metric topology transport covers both the quotient in the product domain and the quotient target. The compactness of the original quotient is also transported through that same equality. No new metric or smooth-metric certificate is assumed.',
    'The native ordered-factor freezing statement uses the exact original factor Q and the exact order exp(bV)*Q*exp(mV). Neither commutativity nor normality of Gamma is assumed. The actual quotient action is used.',
    'The probability discrepancy loss uses actual total mass one and support-wise test errors under both laws. Reweighting selection uses a true convex vector and sum of absolute weight differences; its retained discrepancy is independent of the number of subboxes or residue pieces.',
    'Uniform Lipschitz control (or proved uniform Lipschitz approximation with controlled error) for induced tests on the smaller quotients remains a separate obligation. This freezing result alone does not establish the dimension induction or exact residue sampling weights.',
    'All retained source hashes and transitive axiom sets are unchanged. These are author-side checks, not independent kernel replay.',
]
source = source[:a] + 'application_review=COMPONENTS+' + repr(review) + '+[REMAINING],\n        ' + source[b:]
source = re.sub("reference_scope='[^']*'", "reference_scope='06_rough_progressions slow-factor freezing and convex discrepancy preservation'", source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print('Prepared audit for', len(modules), 'modules.')
