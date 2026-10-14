from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-period-correlation-transfer-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-period-correlation-transfer-audit.py').read_text(encoding='utf-8')
source = source.replace('"""Register and audit exact period correlation extraction and native integer-cell rebasing."""',
    '"""Register and audit original harmonic correlator transfer and the good-cell projection implication."""')
source = source.replace("PREFIX = 'round-period-correlation-transfer'", "PREFIX = 'round-harmonic-correlator-transfer'")
source = source.replace("OLD = 'round-cyclic-interval-powers'", "OLD = 'round-period-correlation-transfer'")
modules = ['Hindman168/CompleteCellBoundedHarmonicError.lean',
           'Hindman168/NativeHarmonicCellCorrelation.lean',
           'Hindman168/NativePieceRestriction.lean',
           'Hindman168/HarmonicGoodCellCorrelation.lean',
           'Hindman168/OriginalCellCorrelationSum.lean',
           'Hindman168/NativeGoodCellProjectionLower.lean']
components = ['The original conditional harmonic-cell comparison now holds for every real test bounded by any nonnegative B, including B=0, with error B*Mq/(kMq). Its actual unnormalized and arbitrary finite-cell aggregate versions retain every original cell mass; the aggregate error is total cell mass times B*Mq/X. The native period correlator transport now gives a real conditional harmonic-cell correlation at least its original threshold minus B*Mq/X, preserving the original native manifold, step and observable bounds. Arbitrary stage-and-piece restriction of a native represented family to zero now preserves its original geometry and uniform observable bounds. The good-cell Gowers mass estimate is integrated using the actual conditional probabilities mass(C)/sum mass(C). Given unit tests with correlation at least gamma on good cells and zero on bad-cell points, the normalized original harmonic cell correlation is at least delta^(2^d)*gamma/2 - Mq/X. A finite-mass test vanishing outside a selected finite set has exactly its original expectation summed over that set, even if the original mass has support elsewhere. Distinct original complete residue cells are disjoint, so a global unit test zero outside their union has original integer expectation at least their actual total mass times this good-cell correlation bound. For an actual unit native represented family with these displayed good-cell correlations, actual complete-cell mass tending to one and actual Mq/X tending to zero imply fine native projection norm at least delta^(2^d)*gamma/2 along the same ultrafilter, on the original integer harmonic Hilbert law. This proves the correlation-to-projection implication with its actual weights and boundary loss. The existence and uniform finite-list selection of the inverse correlators remain missing; no such existence is inserted as an axiom or hidden premise of the final original problem.']
gap = 'Inverse correlator existence and its quantitative finite-list application to the fine projection, and remaining replica integration remain missing.'
assert gap in previous.REMAINING
remaining = previous.REMAINING.replace(gap, components[0] +
    ' Inverse correlator existence and uniform finite-list assembly of the native good-cell family, discharge of the displayed actual master-law geometry and limit inputs, and remaining replica integration remain missing.')
for field, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + field + r' = .*$', field + ' = ' + repr(value), source, flags=re.M)
counts = {'1165': '1172', '1154': '1160', '5384': '5394', '1172': '1178', '1163': '1169'}
source = re.sub(r'\b(?:1165|1154|5384|1172|1163)\b', lambda m: counts[m.group()], source)
source = source.replace('== len(set(names)) == 24', '== len(set(names)) == 10')
source = source.replace("'selected_report_count': 24", "'selected_report_count': 10")
source = source.replace('len(names) == 24', 'len(names) == 10')
source = source.replace("for kind, _ in values) == 22", "for kind, _ in values) == 10")
source = source.replace("'theorem_count': 22", "'theorem_count': 10")
source = source.replace('new_theorems=22', 'new_theorems=10')
source = source.replace('new_theorem_count=22', 'new_theorem_count=10')
source = source.replace('new_definitions=2', 'new_definitions=0')
source = source.replace('new_axiom_reports=24', 'new_axiom_reports=10')
source = source.replace('new_module_count=7', 'new_module_count=6')
source = source.replace('new_selected_report_count=24', 'new_selected_report_count=10')
review = [
    'PROGRESS. The preceding exact period extraction, real phase conversion and native integer-cell rebasing round was rechecked terminal-successfully before edits. Its authoritative manifest was copied unchanged to this saved baseline. Retained proof-source hashes and selected kernel axiom sets remain unchanged; only root imports and the kernel declaration registry change among retained files.',
    'The actual conditional harmonic-cell error for unit tests is extended to any nonnegative bound B. If B=0, every test value is proved exactly zero and both averages vanish. If B>0, divide the actual test by B, apply the retained unit-test comparison, and use the exact finite sum and Haar scaling identities to multiply the resulting inequality back by B. The original conditional harmonic denominator and all original coefficients are retained.',
    'Actual positivity of each complete-cell mass converts conditional error to the unnormalized mass-weighted error. The finite aggregate sums these errors over the original labeled cells, bounds kMq below by X and keeps the common nonnegative observable bound B. The resulting error is sum of actual cell masses times B*Mq/X. No uniform-weight replacement, cardinality estimate or altered arithmetic scale is used.',
    'The retained native complete-cell period transport supplies the actual real observable, original globally anchored orbit and uniform cell correlation. For a unit integer input, multiplying it by that B-bounded observable gives an actual B-bounded real test at every integer point. The proved conditional harmonic error and kMq >= X show that its harmonic correlation is at least the original threshold minus B*Mq/X. The same original native data object, step, supremum bound and Lipschitz bound remain present.',
    'Native stage-and-piece restriction changes each selected observable to the constant zero observable on rejected labels. A single original nonnegative bound and Lipschitz constant cover both branches, while all original translating elements and basepoints are retained. The exact original interval-residue piece map determines the branch at every integer point. This proves a genuine native representation closure needed to put zero on bad cells or unused complete-cell labels, rather than assuming arbitrary indicator multiplication preserves the native subspace.',
    'The good-cell mass estimate is applied to the actual probabilities p_C = mass(C)/sum mass(C), with positive masses and exact total one. The actual cyclic cell input is the original integer function at kMq+r+M*z.val. On good cells its selected unit test has displayed correlation at least gamma; on bad cells only the actual original cell-point values must vanish. That latter condition allows one global test to remain nonzero on other cells. Multiplying the good-cell mass lower bound by nonnegative gamma and summing the local correlations gives the actual weighted uniform bound. The retained unnormalized harmonic aggregate comparison then yields the normalized original harmonic lower bound delta^(2^d)*gamma/2 - Mq/X.',
    'The finite-mass expectation identity cancels sums outside a selected finite set only where the test is actually zero; mass outside the set is not discarded or renormalized. The proof passes through the actual intersection of the original mass support and that set, using zero test values on one tail and zero mass coefficients on the other. The existing complete residue-cell disjointness and union-sum identities then identify the global original integer expectation exactly with the sum of its actual complete-cell correlations. The lower bound retains the actual total mass of complete cells, including the genuine boundary loss.',
    'For an actual bounded Hilbert family represented in the original native nilspace and bounded by one, the displayed good-cell correlations and zero outside the complete-cell union give original expectation at least T_w*(a-rho_w), with a=delta^(2^d)*gamma/2, T_w the actual complete-cell mass and rho_w=M_w*q_w/X_w. The actual hypotheses T_w -> 1 and rho_w -> 0 give err_w=a*(1-T_w)+T_w*rho_w -> 0. Positive complete-cell mass eventually supplies nonempty actual cell labels; no permanent nonemptiness hypothesis is needed. The retained original-law native correlation-to-projection theorem then gives projection norm at least a along the same ultrafilter. Neither T_w nor rho_w is replaced by an assumed limit value at finite stages.',
    'All proof inputs are explicit: the native good-cell family, its actual unit bound, local correlations, zero branches and original master-law geometry and limit hypotheses. This round proves their transport and correlation-to-projection implication. It does not construct the missing inverse-theorem correlators or discharge all master-law inputs and therefore does not prove the unconditional subgroup inverse lemma or StrongConjecture. The original target remains unchanged.',
    'Development failures and warnings are excluded from verification evidence. The zero-bound simplification keeps the actual zero multiplier. The original Finsupp API is notMem_support_iff. Subsequent focused checks use the project setting autoImplicit=false. No set_option or increased resource limit occurs in any new source. Only terminal warning-free focused compilations, the full build and complete selected kernel output count as verification.',
    'Six modules contain ten proved theorems and no definitions or instances. All ten new declarations are selected for transitive axiom audit; the fifteen retained axiom-free declarations remain unchanged. Original weights, period coordinates, native manifold data and projection spaces are preserved. Inverse correlator existence and uniform finite-list assembly of the good-cell family, actual master-law geometry and limit instantiation, remaining replica integration, calibration and final original monochromatic extraction remain missing. StrongConjecture is unproved. No unavoidable blocker is established; publication, PR and prize claim remain pending.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='05_prediction: original harmonic-cell correlator transfer, good-cell mass integration, original integer expectation and conditional native fine-projection lower bound')\n"
) + source[end:]
Path('round-harmonic-correlator-transfer-audit.py').write_text(source, encoding='utf-8')
print('Prepared six-module audit: ten theorems, no definitions or instances.')
