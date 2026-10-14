from pathlib import Path
import ast
import json
import re

previous = 'round-master-inverse-short-cube'
prefix = 'round-selected-native-short-cube'
modules = ['Hindman168/MasterModelDifferenceShortCube.lean',
           'Hindman168/SelectedNativeShortCubeModels.lean',
           'Hindman168/SelectedNativeChainShortCubeModels.lean']
components = [
    'Given the explicitly unproved finite-list periodic interval inverse input, the original '
    'difference of two actual [0,1]-valued master Hilbert families has the uniform short-cube '
    'estimate at natural master indices. The difference is formed in the actual original '
    'weighted space, its pointwise unit bound is proved, and the completion preserves its '
    'subtraction exactly. A constant finite-index map is identified with the canonical '
    'masterGapIndex as a function, retaining the original cutoff, gap and prime law.',
    'The positive short-cube quotient J and projection threshold are chosen first; the coarse '
    'error is then chosen as one quarter of that threshold, before the energy-selection '
    'master count N. For every sufficiently large constructed master count and every actual '
    'bounded input family, energy selection supplies the same coarse native model at each '
    'block and label. Its fine projection error is at most twice the coarse error and strictly '
    'below the inverse threshold. Thus at every permissible earlier selected padding its '
    'original conditioned prime-tuple expectation of the absolute integer short-cube '
    'statistic is below the requested error, with unchanged arithmetic coordinates.',
    'All finite principal tails, blocks and labels are selected simultaneously. For every '
    'actual chain on the principal indices, the first pivot determines one common fine '
    'padding valid for all chain blocks. Exact tail-position recovery identifies the same '
    'previously selected models. Every original model-difference short cube at that padding '
    'has the requested eventual bound along the original ultrafilter. Finite native products '
    'give one common actual native nilmanifold and uniform observable bounds, retaining '
    'each model own coarse interval partition. The inverse existence input remains unproved.'
]
reviews = [
    'PROGRESS. The preceding master inverse short-cube round was terminal-successfully '
    'rechecked before any proof edit. Its authoritative manifest was copied as the saved '
    'baseline. Retained proof-source hashes and selected kernel axiom sets are unchanged '
    'except the necessary root imports and declaration registry.',
    'The model difference uses the subtraction operation of boundedHilbertFamilies in the '
    'original integerMass space. Its pointwise absolute bound is derived from both [0,1] '
    'bounds, and the actual linear completion map identifies its completion with the '
    'difference of the two completions. No separate abstract error vector substitutes for '
    'the original integer input.',
    'Natural master indices are transferred to constant Fin M maps whose values reduce '
    'definitionally to the original natural indices. Function extensionality proves that '
    'the constant fine map is exactly masterGapIndex. This identifies the fine projection '
    'without transporting a dependent Hilbert-family argument through a simplified mass '
    'equality. The original cutoff, polynomial modulus, gap and conditioned good-tuple '
    'law are all retained.',
    'J and the positive inverse projection threshold are selected from the cube dimension '
    'and requested error before the master count or any arithmetic data. The coarse '
    'accuracy is threshold/4, so twice that accuracy is strictly below the threshold. '
    'Only afterwards does the proved energy-selection theorem choose its Ramsey count. '
    'Master conditions discharge the canonical gap divisibility, and unit bounded inputs '
    'satisfy the original subprobability Hilbert hypotheses at every stage.',
    'At each selected tail, block and label, a single native coarse model retains its unit '
    'bound and coarse approximation. For every admissible earlier selected padding its '
    'proved projection bound is at most twice the coarse error. The previous original '
    'model-difference estimate then gives the original absolute short-cube expectation '
    'below the requested error. No Bessel, projection or short-cube conclusion is supplied '
    'as a new assumption.',
    'Finite choice selects models simultaneously for all finite principal tail positions, '
    'blocks and labels. Exact principalTailPositions_image recovers each chain tail. '
    'The selected_chain_common_padding theorem supplies a single earlier fine padding '
    'for every block of the actual chain, and all original model-difference statistics '
    'there have the same requested bound with the same J. The chain coordinate map is '
    'strictly increasing and its principal indices are the actual chain pivots.',
    'The retained finite varying-gap product construction gives one native manifold, '
    'one observable absolute bound and one Lipschitz bound for the finite selected family. '
    'Each model keeps its own coarse gap and its actual original function values. '
    'No fixed finite list of correlators is assumed for this construction.',
    'A failed dependent simplification approach was repaired before registration by '
    'identifying index maps as functions and using definitionally constant pivot values. '
    'Development errors and failed focused checks are excluded from verification evidence. '
    'Only warning-free terminal focused checks, the complete successful build and the '
    'complete selected kernel output count. No resource increase or set_option occurs.',
    'Three new modules contain three theorems, all selected for transitive kernel audit. '
    'The sixteen retained axiom-free declarations remain unchanged. The explicit '
    'HasNativePeriodicIntervalInverse proposition remains unproved, and StrongConjecture '
    'remains unchanged and unproved. This round supplies the actual conditional '
    'energy-selection-to-chain-short-cube bridge; it does not prove the interval inverse '
    'existence theorem, all correlation integration, Calibration/Alignment or final '
    'monochromatic extraction. No unavoidable blocker is established; publication, '
    'prize PR and claim remain pending.'
]

source = Path(previous + '-audit.py').read_text(encoding='utf-8')
remaining_line = re.search(r'^REMAINING = (.+)$', source, re.M)
remaining = ast.literal_eval(remaining_line.group(1))
marker = 'The finite-list interval inverse existence statement itself'
assert marker in remaining
remaining = remaining.replace(marker, ' '.join(components) + ' ' + marker, 1)
source = source.replace("PREFIX = '" + previous + "'", "PREFIX = '" + prefix + "'")
source = source.replace("OLD = 'round-native-local-correlator-synthesis'", "OLD = '" + previous + "'")
source = re.sub(r'^MODULES = .+$', 'MODULES = ' + repr(modules), source, count=1, flags=re.M)
source = re.sub(r'^COMPONENTS = .+$', 'COMPONENTS = ' + repr(components), source, count=1, flags=re.M)
source = re.sub(r'^REMAINING = .+$', 'REMAINING = ' + repr(remaining), source, count=1, flags=re.M)
numbers = {'1192': '1198', '1180': '1183', '1189': '1192', '1198': '1201', '5431': '5434'}
source = re.sub(r'\b(?:1192|1180|1189|1198|5431)\b', lambda m: numbers[m.group()], source)
source = source.replace('== 13', '== 3')
source = source.replace("for kind, _ in values) == 9", "for kind, _ in values) == 3")
source = source.replace('new_theorems=9, new_definitions=4', 'new_theorems=3, new_definitions=0')
source = source.replace('new_axiom_reports=13', 'new_axiom_reports=3')
source = source.replace('new_module_count=6, new_theorem_count=9', 'new_module_count=3, new_theorem_count=3')
source = source.replace('new_selected_report_count=13', 'new_selected_report_count=3')
source = source.replace("'theorem_count': 9, 'selected_report_count': 13", "'theorem_count': 3, 'selected_report_count': 3")
source = re.sub(r'application_review=\[.*?\], new_modules=MODULES',
                'application_review=' + repr(reviews) + ', new_modules=MODULES', source, count=1, flags=re.S)
source = source.replace('05_prediction: exact original cell-law alignment and uniform inverse short-cube threshold before choosing N',
                        '05_prediction: pre-Ramsey thresholds and actual selected native model differences on every chain')
source = source.replace('Register and audit exact master-law identities and uniform inverse short-cube integration.',
                        'Register and audit the actual selected native model short-cube bridge.')
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
ast.parse(source)
print(json.dumps({'modules': modules, 'theorems': 3, 'definitions': 0, 'reports': 3}))
