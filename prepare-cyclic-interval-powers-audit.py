from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-interval-cube-geometry-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-interval-cube-geometry-audit.py').read_text(encoding='utf-8')
source = source.replace('"""Register and audit the actual product quotient and representation increment against its saved baseline."""',
    '"""Register and audit the actual cyclic-to-interval power and positive-norm transfer."""')
source = source.replace("PREFIX = 'round-interval-cube-geometry'", "PREFIX = 'round-cyclic-interval-powers'")
source = source.replace("OLD = 'round-master-short-bessel'", "OLD = 'round-interval-cube-geometry'")
modules = ['Hindman168/FiniteTranslateSumError.lean',
           'Hindman168/IntegerIntervalPeriodicMean.lean',
           'Hindman168/IntegerIntervalCubeRealLowerBound.lean',
           'Hindman168/CyclicIntervalCubeTransfer.lean',
           'Hindman168/CyclicIntervalUniformPeriodError.lean',
           'Hindman168/CyclicIntervalPositiveNormTransfer.lean']
components = ['The full signed-increment integer interval cube mean of the periodically extended cyclic input is now defined. The finite translated-sum discrepancy is bounded by both forward and backward departing-set cardinalities, with the common intersection canceled exactly. Both actual interval boundary counts therefore control the normalized translated mean. Finite Haar averaging of the canonical residue translates gives exactly the original cyclic cube mean, and their uniform displacement bounds yield the full normalized interval-versus-cyclic cube-power error. A floor-width parameter box gives actual domain cardinality at least (L/(2(d+1)))^(d+1) whenever L >= d+1. The normalized error is consequently at most C_d q/L, with the explicit positive dimension-only constant C_d = 2 * 2^d * (d+1) * (2(d+1))^(d+1). At L=Kq this is at most C_d/K for all positive cyclic moduli, all K >= d+1 and all unit real inputs. For every positive dimension and positive cyclic norm threshold delta, one fixed K depending only on d and delta retains a positive actual interval cube mean and interval dyadic root at least delta/2, uniformly over q and the input. No inverse correlator existence is assumed or proved by this transfer.']
gap = 'The normalized cyclic-to-interval error bound and inverse correlator transfer, remaining replica integration and inverse correlator existence remain missing.'
assert gap in previous.REMAINING
remaining = previous.REMAINING.replace(gap, components[0] +
    ' Period correlation extraction and inverse correlator transfer, remaining replica integration and inverse correlator existence remain missing.')
for field, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + field + r' = .*$', field + ' = ' + repr(value), source, flags=re.M)
components[0] = components[0].replace('all K >= d+1', 'every positive K')
remaining = remaining.replace('all K >= d+1', 'every positive K')
source = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), source, flags=re.M)
source = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), source, flags=re.M)
counts = {'1153': '1159', '1141': '1147', '5341': '5360', '1159': '1165', '1150': '1156'}
source = re.sub(r'\b(?:1153|1141|5341|1159|1150)\b', lambda m: counts[m.group()], source)
source = source.replace('== len(set(names)) == 18', '== len(set(names)) == 19')
source = source.replace("'selected_report_count': 18", "'selected_report_count': 19")
source = source.replace('len(names) == 18', 'len(names) == 19')
source = source.replace("for kind, _ in values) == 13", "for kind, _ in values) == 16")
source = source.replace("'theorem_count': 13", "'theorem_count': 16")
source = source.replace('new_theorems=13', 'new_theorems=16')
source = source.replace('new_theorem_count=13', 'new_theorem_count=16')
source = source.replace('new_definitions=5', 'new_definitions=3')
source = source.replace('new_axiom_reports=18', 'new_axiom_reports=19')
source = source.replace('new_selected_report_count=18', 'new_selected_report_count=19')
review = [
    'PROGRESS. The previous eligibility response rechecked official submission rules but did not change proof code. This continuation resumed the pending exact cyclic-to-interval proof chain. Before registration the saved baseline was verified identical to the authoritative manifest and all 1159 retained source/config hashes were rechecked unchanged. The earlier complete geometry round supplied the actual domain, both boundary counts and pointwise residue averaging.',
    'For two finite sets, the common intersection cancels exactly. The sum difference is the difference of the two set-difference sums, each bounded by its actual cardinality for a unit real test. Mapping the original set by a group translation gives the translated sum; the forward departing set bounds the new points, while the backward departing set is exactly the missing points. Both sides remain present. The generic finite-set difference and translation lemmas explicitly take DecidableEq, so concrete applications use the same member-test instances and compile within the default heartbeat limit.',
    'The interval cube mean is the actual periodic cube product averaged over the full signed-increment integer parameter domain. The unit-product bound and both retained departure counts give translated-mean error at most 2 * 2^d * D * L^d / card(A_L), for positive L. The denominator is proved positive using the actual domain nonemptiness theorem. No positive-increment-only average or altered vertex law is substituted.',
    'The retained finite Haar/finite-sum commutation theorem exchanges the actual domain sum with canonical residue averaging. The exact pointwise residue-translate identity then makes the averaged translated mean equal to the full cyclic cube mean. Finite Haar absolute-error averaging and the canonical displacement bound D=(d+1)(q-1) yield the normalized discrepancy. Averaging uses the original finite cyclic parameter law, not an equidistribution premise.',
    'The genuine root/increment box of width floor(L/(d+1)) lies in the full domain. The natural division-remainder identity and L >= d+1 imply L <= 2(d+1)floor(L/(d+1)). Raising the resulting real width lower bound to d+1 gives card(A_L) >= (L/(2(d+1)))^(d+1). This weaker lower-count constant has the same interval power as the paper estimate and suffices for its dimension-only error; it does not change the integration domain.',
    'Replacing (d+1)(q-1) by (d+1)q in the numerator and applying the positive domain lower bound gives the explicit uniform error C_d*q/L. The audited field identity cancels the interval powers. For L=Kq and K >= d+1, q positivity proves L positivity and the range condition; canceling q gives C_d/K. The modulus, number of periods and unit input remain quantified, and C_d is positive and depends only on dimension.',
    'For positive d and delta, the difference delta^(2^d)-(delta/2)^(2^d) is strictly positive. An Archimedean choice of K depending only on d and delta makes C_d/K smaller than this gap. The actual cyclic Gowers power identity and the discrepancy bound then force the actual interval cube mean strictly above (delta/2)^(2^d). Thus the interval mean is positive before the dyadic real-root power identity is used. Monotonicity of nonnegative integer powers yields interval root at least delta/2. No global positivity or triangle inequality for every interval input is claimed.',
    'Development failures do not count as validation evidence. A duplicate Haar-sum theorem was removed in favor of the retained theorem. Explicit decidable equality fixed finite-boundary elaboration without set_option or increased resource limits. A redundant ring call after field_simp closed its goal was removed. Only terminal warning-free focused builds, the complete build and all selected kernel reports count as verification.',
    'Six modules contain sixteen proved theorems and three definitions, all nineteen selected for transitive axiom audit. The fifteen retained axiom-free declarations are unchanged. The cyclic-to-interval cube-power error and positive norm transfer are proved on the actual full domain. Period correlation extraction, inverse correlator existence, remaining replica integration, calibration and the final original coloring extraction remain missing. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize claim remain pending.'
]
review.insert(6, 'The actual interval mean of every unit real input has absolute value at most one, directly from its unit cube products and positive domain cardinality. The explicit transfer constant is at least 2(d+1). For every positive K below d+1, the interval and cyclic unit bounds give discrepancy at most two, which is at most C_d/K. Combining this with the geometric large-K estimate proves the stated uniform error for every positive number of periods, including q=1 and dimension zero.')
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='05_prediction: exact cyclic-to-interval cube-power discrepancy and fixed positive norm transfer on K periods')\n"
) + source[end:]
Path('round-cyclic-interval-powers-audit.py').write_text(source, encoding='utf-8')
print('Prepared six-module audit: sixteen theorems, three definitions.')
