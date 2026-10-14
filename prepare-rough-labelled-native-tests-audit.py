from pathlib import Path
import re

prefix = 'round-rough-labelled-native-tests'
stems = ['RoughNativeResidueProductApproximation', 'RoughNativeLabelledModelResidues',
    'RoughNativeLabelledPieceTests', 'RoughRescaledDependentPieceTest', 'RoughFiniteCofinalSelection']
modules = ['Hindman168/' + s + '.lean' for s in stems]
components = [
    'RoughNativeResidueProductApproximation constructs one uniformly Lipschitz bounded observable on each actual packaged kernel quotient for every bounded frozen scalar and original observable. Its estimate holds for every actual kernel point and every right factor in the original specified residue coset, keeping the original ordered product.',
    'RoughNativeLabelledModelResidues chooses one member of Fin K for every actual geometric box label before the spatial sample. The original joint rational model exponential at every integer sample equals that finite residue exponential in the original quotient.',
    'RoughNativeLabelledPieceTests chooses one fixed positive natural partition count and one uniform new Lipschitz bound before all original progression/model/box/map/test data. It constructs the actual label-to-finite-quotient indices and dependent quotient observable family, retaining the original supremum bound. At every original-box integer sample the error from the original test to the constructed actual kernel quotient test is at most freezing error plus approximation error.',
    'RoughRescaledDependentPieceTest proves exact selected-test specialization under x=u+Ky even for label-dependent source spaces and maps. This applies to the actual varying finite kernel quotient domains rather than only to a common scalar test domain.',
    'RoughFiniteCofinalSelection proves that one member of a fixed finite list works for arbitrarily large progression lengths and arbitrarily late scale indices simultaneously. Its generic logical conclusion does not assume that a single scale threshold already works for all lengths or construct the missing bad families.',
]
remaining = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'Actual native label-indexed finite quotient tests are now constructed with fixed partition count and uniform Lipschitz bound before varying data, original-box error bounded by freezing plus approximation, exact dependent test specialization after residue substitution, and finite simultaneous cofinal-choice logic. '
    'Combine these constructions with exact rescaled discrepancy selection and all-real native logarithm polynomial transfer in a complete smaller-dimensional bad-family theorem. '
    'The full quantitative Leibman obstruction and its uniform finite character list, corrected arbitrary-box comparison, stretched-filtration prerequisites, finite density extraction and complete dimension induction/uniform rough-step theorem remain open. '
    'Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs, and final ordered positive rapidly separated monochromatic extraction remains open. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
review = [
    'The combined theorem discharges the formerly explicit native freezing and label-indexed approximation errors using the actual previous constructions. The partition count and new Lipschitz bound are fixed before w,H,q,z,Z, coefficient models, original signed box, group map and test function.',
    'The fixed finite quotient family is indexed by Fin K, where K is the specified original rational vector period. At each integer progression index the actual integer spatial model determines each label index. The family size does not grow with the interpolation denominators, progression length, selected box or coefficient sizes.',
    'Every source quotient uses the exact roughNativeKernelNilmanifold metric. The bounded anchor scalar is derived from actual balanced-box containment and the actual whole-box horizontal error estimate, not assumed independently for every piece.',
    'Actual original sample membership proves membership in its own geometric interval label piece. The combined estimate uses actual native factorization, proved right-coset equality and actual induced-test approximation, without commuting factors or assuming lattice normality.',
    'The constructed native map is defined at all real joint parameters and takes values in the actual character kernel. The approximation conclusion applies on original integer samples; it does not replace the separately proved all-real native logarithmic polynomial identity.',
    'Dependent source-space specialization under x=u+Ky preserves the selected quotient index and both the observable and map. This closes a genuine typing obligation that cannot be met by treating all finite quotient lattices as the same source space.',
    'Finite cofinal choice keeps both length and scale index arbitrarily large. It is a generic logical theorem: actual bad progression families, their restriction/thinning properties and the full smaller-dimensional contradiction still have to be supplied.',
    'All retained proof sources and previous axiom sets remain unchanged. New declarations introduce no sorry, logical axiom, unsafe computation or tactic-limit increase. Author-side checking is not independent kernel replay and does not prove the final target.',
]
source = Path('round-rough-freezing-affine-obstruction-audit.py').read_text(encoding='utf-8')
for name, value in {'PREFIX': prefix, 'OLD': 'round-rough-freezing-affine-obstruction',
        'MODULES': modules, 'COMPONENTS': components, 'REMAINING': remaining}.items():
    source, count = re.subn('^' + name + r'\s*=.*$', lambda _: name + ' = ' + repr(value), source, flags=re.M)
    assert count == 1, name
a = source.index('application_review=COMPONENTS+')
b = source.index('verified=summary', a)
source = source[:a] + 'application_review=COMPONENTS+' + repr(review) + '+[REMAINING],\n        ' + source[b:]
source = re.sub("reference_scope='[^']*'", "reference_scope='06_rough_progressions actual uniformly labelled native kernel quotient tests and simultaneous finite cofinal choice'", source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print('Prepared audit for', len(modules), 'modules.')
