from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-finite-bessel-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-finite-bessel-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-finite-bessel'", "PREFIX = 'round-weighted-bessel-sampling'")
source = source.replace("OLD = 'round-full-concatenation'", "OLD = 'round-finite-bessel'")
modules = ['Hindman168/FiniteWeightedSamplingMoments.lean',
           'Hindman168/FiniteWeightedSampleSelection.lean',
           'Hindman168/WeightedBesselSampleLimit.lean',
           'Hindman168/MixedDualWeightedBesselLimit.lean']
components = ['Direct independent sampling from the original arbitrary real finite weights now has exact centered-sum and empirical-mean variance formulas. Joint positive-budget selection controls squared empirical mean error by 2/M and the off-diagonal sum by twice M squared times the original pair mean plus a positive slack. For varying finite laws with vanishing pair mean, a fixed sample length can be selected at every stage so all off-diagonal pair statistics vanish along the same tail-containing ultrafilter. Combining this selection with the fixed-family projection Bessel bound proves the full arbitrary varying-index weighted Bessel null-limit implication at the paper degree 2d-1. Neither index cardinality nor group cardinality is bounded; original cell probabilities and direction weights are retained exactly.']
gap = 'The fixed finite-family ultrafilter Bessel bound still needs uniform finite thresholds and the sampling/selection passage to arbitrarily large, arbitrarily weighted index families.'
assert gap in previous.REMAINING
remaining = previous.REMAINING.replace(gap, components[0] + ' The varying-index weighted Bessel limit still needs a uniform finite threshold over all finite systems.')
for field, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + field + r' = .*$', field + ' = ' + repr(value), source, flags=re.M)
counts = {'1131': '1138', '1120': '1124', '5271': '5281', '1138': '1142', '1129': '1133'}
source = re.sub(r'\b(?:1131|1120|5271|1138|1129)\b', lambda m: counts[m.group()], source)
source = source.replace('== 16', '== 10').replace("'theorem_count': 16", "'theorem_count': 10")
for a, b in [('new_theorems=16', 'new_theorems=10'),
             ('new_axiom_reports=16', 'new_axiom_reports=10'),
             ('new_module_count=7', 'new_module_count=4'),
             ('new_theorem_count=16', 'new_theorem_count=10'),
             ('new_selected_report_count=16', 'new_selected_report_count=10')]:
    source = source.replace(a, b)
source = source.replace("names = ['Hindman168.' + name for values in ds.values() for _, name in values]",
    "names = [('Hindman168.FiniteMass.' if p in MODULES[:2] else 'Hindman168.') + name for p, values in ds.items() for _, name in values]")
source = source.replace("names = ['Hindman168.' + n for ds in declarations().values() for _, n in ds]",
    "names = [('Hindman168.FiniteMass.' if p in MODULES[:2] else 'Hindman168.') + n for p, ds in declarations().items() for _, n in ds]")
review = [
    'PROGRESS. The finite-family Bessel audit was rechecked before these source additions. All retained proof-source hashes, original dependency pins and previous selected axiom sets are preserved. Only root imports and the selected kernel registry change among the retained source/configuration files.',
    'Two distinct coordinates of the normalized product finite mass have the original independent pair expectation, including arbitrary real weights. Centering the observable kills the off-diagonal terms in the sum-square expansion. Dividing by a positive sample length gives the exact variance formula, and unit bounds give variance at most 1/M. Nonnegativity is used only where required for the probability and inequalities.',
    'A normalized nonnegative finite mass has a support point no larger than its expectation for any real observable. Apply this to X/a+Y/b with both budgets strictly positive and both observables nonnegative. The expected objective is at most two, so a single support point satisfies both doubled budgets. There is no unsupported assertion that the two independent Markov bounds have an intersecting positive-probability event.',
    'The off-diagonal sample statistic includes repeated direction values at distinct sample positions. Those coordinates remain independent and have the original pair mean. Equal-position terms are zero. Each term is bounded by the nonnegative pair mean, giving total expectation at most M squared times that mean. No diagonal vanishing premise or index-size bound is introduced.',
    'At each stage joint selection uses mean-error budget 1/M and pair budget M squared times the original pair mean plus 1/(w+1). The squared mean error is at most 2/M. The positive slack tends to zero along the same tail-containing ultrafilter. Nonnegativity and domination by the selected off-diagonal sum force every distinct-position pair statistic to zero.',
    'The varying-index weighted local Gowers average lies in [0,1] and therefore has an ultrafilter limit a. If a is positive, choose fixed M so both 1/M < (a/2)^(2^d) and 2/M < (a/2)^2. The selected family satisfies all off-diagonal vanishing hypotheses of the already audited fixed-family Bessel theorem, so its limiting mean b has b^(2^d) <= 1/M and b < a/2. The squared error limit also satisfies (b-a)^2 <= 2/M, contradicting the second chosen inequality. Hence a is zero. All originally supplied weights and varying systems are retained.',
    'Development elaboration failures and warnings are not counted as successful validation. An inference failure in the off-diagonal sum domination was repaired with an explicit finite-sum type. No set_option or raised resource bounds are used. Only terminal successful focused compilation, the full build and complete selected kernel output count as verification.',
    'Ten theorems in four modules establish the arbitrary weighted varying-index Bessel limit passage. A uniform finite threshold over all finite systems remains to be derived; this is not yet a complete finitary qualitative Bessel modulus. Inverse correlator existence, original-problem transfers and final extraction remain missing. StrongConjecture is unchanged and unproved; no unavoidable blocker is established.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://arxiv.org/html/1603.07815v4', reference_scope='Section 8 sampling and fixed-family Bessel contradiction; arbitrary weighted varying finite-subgroup specialization')\n"
) + source[end:]
Path('round-weighted-bessel-sampling-audit.py').write_text(source, encoding='utf-8')
print('Prepared four-module audit: ten theorems, explicit finite-mass namespace.')
