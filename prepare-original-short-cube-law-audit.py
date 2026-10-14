from pathlib import Path
import ast
import json
import re

previous = 'round-mask-uniform-detection'
prefix = 'round-original-short-cube-law'
modules = [
    'Hindman168/UniformIntervalPairHaar.lean',
    'Hindman168/IntegerShortCubeSamplingIdentity.lean',
    'Hindman168/MaskEndpointShortCubeIdentity.lean',
    'Hindman168/FiniteConditionedSubsetBound.lean',
    'Hindman168/MaskEndpointShortCubeConditioning.lean',
]
components = [
    'Uniform finite-mass expectations are exactly finite counting averages. Independent '
    'uniform coordinate masses and uniform tensor masses are exactly the corresponding '
    'uniform finite laws. Casting Fin T to the integer interval [0,T) preserves the exact '
    'law, and original paired integer interval sampling equals two independent finite Haar '
    'averages. These identities include T=0 and empty direction types.',
    'Boolean cube vertices are exactly all subset vertices under the explicit cube equivalence. '
    'The actual integerPredictionShortCubeStatistic is exactly the original direction-pair '
    'expectation of its original harmonic cube, with the original polynomial modulus and '
    'quotient-dependent interval length; no cyclic or abstract statistic replaces it.',
    'The actual maskEndpointTargetCube is exactly the original integer short-cube statistic '
    'averaged under its original root-prime law, equivalently the original local good event. '
    'This is an all-stage identity, including zero event masses or zero quotient lengths. '
    'Its absolute value is bounded by the original conditioned mean of absolute statistics.',
    'For nested finite good events, the nonnegative conditioned mean is bounded with the '
    'exact original event-probability ratio. If the stronger event has probability at least '
    'one half, its mean is at most twice the weaker conditioned mean. The actual mask local '
    'good event has probability tending to one by proved catalogue inclusion; therefore '
    'every actual endpoint cube is eventually bounded by twice the short-cube absolute '
    'mean conditioned only on primeSampleGood of the actual local catalogue.',
    'A positive tolerance depending only on the column count and requested correlation error '
    'is now chosen before N and all master parameters. Small original short-cube absolute '
    'mean under the weaker original prime-good law then gives small actual original subset '
    'correlation, uniformly over all supports and admissible functions on one eventual tail. '
    'This proves the actual cube-to-original-correlation bridge, without assuming inverse '
    'existence or that the arbitrary target cube is already small.'
]
reviews = [
    'PROGRESS. The previous pre-master detection round was terminal-successfully rechecked '
    'and its manifest copied before source edits. Retained proof sources and transitive '
    'axiom sets remain unchanged except root imports and the selected declaration registry.',
    'The exact pushforward of uniform Fin T is uniformIntervalMass 0 T. The finite product '
    'and tensor coefficient identities identify the full paired law. A genuine equivalence '
    'between paired direction functions and two direction functions splits the finite Haar '
    'mean. This includes T=0: zero laws on empty types and the singleton empty product are '
    'retained rather than normalized by an assumed positive length.',
    'Boolean vertices are reindexed by the existing cubeSubsetBoolEquiv; the selected '
    'coordinate sum is exactly the subset sum. The original integerMass support lemma '
    'identifies the full window sum with its original expectation. Fubini retains the '
    'direction law before the harmonic root. No cyclic law or sampled approximation enters.',
    'The proved targetPredictionModulus_eq_actual and natAbs of the natural modulus '
    'identify the actual target step. Nat.div_div_eq_div_mul identifies R/P/J with the '
    'retained shift length R/(J*P). The actual direction dimension is definitionally the '
    'targetPredictionOrder. The existing supported-event conditioning identity retains '
    'the original local denominator exclusion and all zero-mass cases.',
    'For a stronger event F contained in E, nonnegative numerator monotonicity gives '
    'the exact bound with event(E)/event(F). Both denominators are proved positive in '
    'this inequality. Under total mass one and event(F)>=1/2 the ratio is at most two. '
    'No bound on the test or assumption that conditioning leaves the distribution unchanged '
    'is used. The local event probability limit is proved from the actual master catalogue, '
    'slot injection and denominator membership.',
    'The endpoint absolute mean is dominated by twice the original primeSampleGood '
    'short-cube absolute mean on one eventual stage, uniformly over all integer targets. '
    'Finite eventual conjunction gives one stage for all supports. Combining this bound '
    'with the preceding pre-master detection tolerance divided by two proves a tolerance '
    'chosen before N, gap data, chains, rational coefficients, J and functions for the '
    'actual original subset correlation. The small short-cube test is the precise input '
    'still to be supplied by selected model integration; it is not asserted unconditionally.',
    'Five modules add fifteen theorems and no definitions or instances. Each focused '
    'compilation passed without warnings, imported dependencies were built successfully '
    'before dependent checks, and the final full build and selected kernel audit pass. '
    'No new resource options or forbidden proof steps occur; the sixteen retained '
    'axiom-free declarations remain unchanged.',
    'Native interval inverse existence remains explicitly unproved. The actual selected '
    'native model estimates must still be transported through the concrete prime-slot '
    'renaming and common master data to supply these local short-cube inputs. The full '
    'Prediction Principle, Calibration/Alignment and final ordered rapidly separated '
    'monochromatic witness remain incomplete. StrongConjecture remains unproved; no '
    'unavoidable blocker is established and publication or prize submission is not claimed.'
]
source = Path(previous + '-audit.py').read_text(encoding='utf-8')
remaining = ast.literal_eval(re.search(r'^REMAINING = (.+)$', source, re.M).group(1))
marker = 'The finite-list interval inverse existence statement itself'
assert marker in remaining
remaining = remaining.replace(marker, ' '.join(components) + ' ' + marker, 1)
source = source.replace("PREFIX = '" + previous + "'", "PREFIX = '" + prefix + "'")
source = source.replace("OLD = 'round-finite-order-native-prediction'", "OLD = '" + previous + "'")
for name, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + name + r' = .+$', name + ' = ' + repr(value), source, count=1, flags=re.M)
numbers = {'1205': '1206', '1206': '1211', '1188': '1193', '1197': '1202', '5444': '5459'}
source = re.sub(r'\b(?:1205|1206|1188|1197|5444)\b', lambda m: numbers[m.group()], source)
source = source.replace('== 5\n', '== 15\n')
source = source.replace('for kind, _ in values) == 4', 'for kind, _ in values) == 15')
source = source.replace("'theorem_count': 4, 'selected_report_count': 5", "'theorem_count': 15, 'selected_report_count': 15")
source = source.replace('new_theorems=4, new_definitions=1', 'new_theorems=15, new_definitions=0')
source = source.replace('new_axiom_reports=5', 'new_axiom_reports=15')
source = source.replace('new_module_count=1, new_theorem_count=4', 'new_module_count=5, new_theorem_count=15')
source = source.replace('new_selected_report_count=5', 'new_selected_report_count=15')
source = source.replace("names = ['Hindman168.' + name for p, values in ds.items() for _, name in values]",
    "names = [('Hindman168.FiniteMass.' if p.endswith('FiniteConditionedSubsetBound.lean') else 'Hindman168.') + name for p, values in ds.items() for _, name in values]")
source = source.replace("names = ['Hindman168.' + n for p, ds in declarations().items() for _, n in ds]",
    "names = [('Hindman168.FiniteMass.' if p.endswith('FiniteConditionedSubsetBound.lean') else 'Hindman168.') + n for p, ds in declarations().items() for _, n in ds]")
source = re.sub(r'application_review=\[.*?\], new_modules=MODULES',
                'application_review=' + repr(reviews) + ', new_modules=MODULES', source, count=1, flags=re.S)
source = source.replace('05_prediction: actual original target-cube detection tolerance chosen before the master count',
                        '05_prediction: exact original short-cube sampling and local conditioned-law detection of subset correlation')
source = source.replace('Register and audit the original pre-master target-cube detection tolerance.',
                        'Register and audit the original short-cube sampling and conditioning bridge.')
ast.parse(source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules': modules, 'theorems': 15, 'definitions': 0, 'reports': 15}))
