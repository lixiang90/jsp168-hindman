from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-uniform-bessel-modulus-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-weighted-bessel-sampling-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-weighted-bessel-sampling'", "PREFIX = 'round-master-short-bessel'")
source = source.replace("OLD = 'round-finite-bessel'", "OLD = 'round-uniform-bessel-modulus'")
modules = ['Hindman168/ConditionedDyadicTupleSupport.lean',
           'Hindman168/IntegerPredictionShortCubeStatistic.lean',
           'Hindman168/MasterShortCubeBesselBudget.lean',
           'Hindman168/MasterShortCubeGlobalThreshold.lean']
components = ['The original conditioned common-pool prime-tuple support now explicitly retains both pool membership and every polynomial nonvanishing condition. The actual original harmonic short-increment cube statistic is defined with the original tuple-dependent polynomial step and quotient length. Integrating the retained short-cube estimate over this exact good-tuple law and applying the proved actual-cell Bessel bound gives a finite explicit error budget: (2J)^d times the selected local-norm budget, plus 4d/J and the boundary error. The subgroup degree is exactly 2^d and the global concatenated degree exactly 2*(2^d)-1. For every requested positive error, one fixed positive integer J and one positive global Gowers threshold now make the actual original mean of absolute short-cube statistics small eventually, uniformly over all unit integer inputs. All original harmonic cell probabilities, conditioned prime weights and varying cyclic lengths are retained.']
gap = 'Remaining short-cube and replica integration, cyclic-to-interval transfer and inverse correlator existence remain missing.'
assert gap in previous.REMAINING
remaining = previous.REMAINING.replace(gap, components[0] +
    ' The single original short-cube mean is now controlled from a positive global norm threshold. Remaining replica integration, cyclic-to-interval transfer and inverse correlator existence remain missing.')
for field, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + field + r' = .*$', field + ' = ' + repr(value), source, flags=re.M)
counts = {'1138': '1149', '1124': '1135', '5281': '5323', '1142': '1153', '1133': '1144'}
source = re.sub(r'\b(?:1138|1124|5281|1142|1133)\b', lambda m: counts[m.group()], source)
source = source.replace("('Hindman168.FiniteMass.' if p in MODULES[:2] else 'Hindman168.')", "'Hindman168.'")
source = source.replace('== len(set(names)) == 10', '== len(set(names)) == 4')
source = source.replace("for kind, _ in values) == 10", "for kind, _ in values) == 3")
source = source.replace("'theorem_count': 10", "'theorem_count': 3, 'selected_report_count': 4")
source = source.replace("len(names) == 10", "len(names) == 4")
for a, b in [('new_theorems=10', 'new_theorems=3'),
             ('new_definitions=0', 'new_definitions=1'),
             ('new_axiom_reports=10', 'new_axiom_reports=4'),
             ('new_theorem_count=10', 'new_theorem_count=3'),
             ('new_selected_report_count=10', 'new_selected_report_count=4')]:
    source = source.replace(a, b)
review = [
    'PROGRESS. The uniform Bessel modulus round was rechecked before edits, and its exact manifest was saved as the baseline. All retained proof-source hashes, dependency pins and previous selected transitive axiom sets are preserved. Only root imports and the selected kernel registry change among retained files.',
    'The supported conditioned tuple belongs to the support of the original product law, so every coordinate remains in its actual dyadic prime pool. If the original polynomial good event were false, the conditioned coefficient would be zero, contradicting support membership. Thus every polynomial in the declared good-event family is nonzero at every supported tuple. No extra nonvanishing assumption is supplied for those tuples.',
    'The named statistic is exactly the original integer harmonic cube on [X,X squared), with each tuple original polynomial step P and short quotient length floor(R/P)/J. It is not replaced by a cyclic-cell statistic. The retained common-cyclic short-cube estimate bounds its absolute value by (2J)^d times the actual degree 2^d subgroup norm, plus 4d/J and the boundary error, on every supported tuple.',
    'The two original interfaces choose different Fintype instances for the same finite subgroup. Their equality is proved explicitly by the standard Fintype subsingleton instance and rewritten in the retained per-tuple estimate before matching it to the original Bessel norm. This avoids a development elaboration timeout without increasing resource bounds, changing the measure or assuming enumeration invariance.',
    'Support-restricted expectation monotonicity integrates the genuine pointwise estimate under the original conditioned law. Its positive good-event limit supplies normalization, so constant errors remain unchanged under expectation. The actual-cell Bessel theorem bounds the integrated degree 2^d norm by the selected positive budget when the actual full-group degree 2*(2^d)-1 norm meets its proved positive threshold. Multiplication by the positive coefficient and explicit expectation linearity give the finite error budget.',
    'For any positive epsilon, the Archimedean choice J > 16(d+1)/epsilon gives 4d/J < epsilon/4. Choose the local budget epsilon/(4*(2J)^d) and the boundary error epsilon/4. The first budget contributes exactly epsilon/4 after scaling. The resulting total is strictly below epsilon. Both J and the global norm threshold are fixed before the stage and input are selected; the eventual estimate is uniform over every integer unit input.',
    'Development failures and warnings are excluded from validation evidence. The finite-subgroup instance mismatch was repaired with explicit instance equality; the final affine strict inequality uses linear arithmetic. No set_option or raised heartbeat bound appears in any new source. Only terminal successful warning-free focused compilation, full build and complete selected kernel output count as verification.',
    'Four modules contain three proved theorems and one definition, each individually registered for transitive axiom checking. This closes the original single short-cube transfer from a small global norm to a small good-tuple mean. It does not prove the inverse correlator existence needed to obtain that norm bound from nilsequence projections, remaining replica integration, cyclic-to-interval inverse transfer, final Calibration/Alignment or original monochromatic extraction. StrongConjecture remains unchanged and unproved. No unavoidable blocker is established; publication, PR and prize claim remain pending the complete proof.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='05_prediction: prediction-cube-subgroup-bound and Combining the subgroups; original fixed-J short-cube and actual harmonic-cell specialization')\n"
) + source[end:]
Path('round-master-short-bessel-audit.py').write_text(source, encoding='utf-8')
print('Prepared four-module audit: three theorems, one definition.')
