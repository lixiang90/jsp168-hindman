from pathlib import Path
import ast
import json
import re

previous = 'round-finite-order-native-prediction'
prefix = 'round-mask-uniform-detection'
modules = ['Hindman168/MaskUniformDetectionThreshold.lean']
components = [
    'The actual target-cube detection tolerance now has a strictly positive common lower bound '
    'depending only on the number of columns and the requested correlation error. Its explicit '
    'formula uses min(epsilon,1), the proved common upper bound on mask-correlation powers, and '
    'the actual output coefficient. It is chosen before N, arithmetic data, chains, quotient '
    'scales or target supports.',
    'The retained original powered subset-correlation theorem proves that this same tolerance '
    'detects every target support on one eventual tail. Arbitrary positive errors are covered, '
    'including errors above one, without requiring a bound on the original correlation. '
    'An existential theorem puts this positive tolerance before all master parameters. '
    'No arbitrary target-cube smallness or inverse existence is asserted.'
]
reviews = [
    'PROGRESS. The preceding finite-order native prediction round was terminal-successfully '
    'rechecked before edits and its manifest copied to the saved baseline. All retained proof '
    'sources and selected kernel axiom sets remain unchanged except root imports and registry.',
    'For p at most the proved column-only power bound P, and 0<a=min(epsilon,1)<=1, '
    'a^P<=a^p<=epsilon^p. Dividing by the actual positive coefficient gives a common positive '
    'lower tolerance for every original support-specific tolerance. The comparison holds for '
    'all positive epsilon and for every master count N.',
    'Finite eventual conjunction applies the retained original subset-correlation detection '
    'theorem to every target support. The resulting event is uniform over admissible integer '
    'functions and all target supports; its stage may depend on the later arithmetic and chain '
    'parameters, while the tolerance does not. The existential declaration explicitly selects '
    'the tolerance before those parameters.',
    'One module adds four theorems and one definition, all selected for transitive kernel audit. '
    'Focused compilation, complete build and selected kernel audit are warning-free and '
    'terminal-successful. No new resource options, axioms, sorry or unsafe proof steps occur.',
    'This proves parameter order for cube-to-correlation detection. Actual model short-cube '
    'bounds still require integration with the local original sampling law and the explicitly '
    'unproved native interval inverse. StrongConjecture remains unproved; the complete Prediction '
    'Principle, Calibration/Alignment and final monochromatic extraction remain incomplete. '
    'No unavoidable blocker is established and no complete prize submission is claimed.'
]
source = Path(previous + '-audit.py').read_text(encoding='utf-8')
remaining = ast.literal_eval(re.search(r'^REMAINING = (.+)$', source, re.M).group(1))
marker = 'The finite-list interval inverse existence statement itself'
assert marker in remaining
remaining = remaining.replace(marker, ' '.join(components) + ' ' + marker, 1)
source = source.replace("PREFIX = '" + previous + "'", "PREFIX = '" + prefix + "'")
source = source.replace("OLD = 'round-selected-native-short-cube'", "OLD = '" + previous + "'")
for name, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + name + r' = .+$', name + ' = ' + repr(value), source, count=1, flags=re.M)
numbers = {'1201': '1205', '1187': '1188', '1196': '1197', '1205': '1206', '5439': '5444'}
source = re.sub(r'\b(?:1201|1187|1196|1205|5439)\b', lambda m: numbers[m.group()], source)
source = source.replace("for kind, _ in values) == 5", "for kind, _ in values) == 4")
source = source.replace("'theorem_count': 5", "'theorem_count': 4")
source = source.replace('new_theorems=5, new_definitions=0', 'new_theorems=4, new_definitions=1')
source = source.replace('new_module_count=4, new_theorem_count=5', 'new_module_count=1, new_theorem_count=4')
source = re.sub(r'application_review=\[.*?\], new_modules=MODULES',
                'application_review=' + repr(reviews) + ', new_modules=MODULES', source, count=1, flags=re.S)
source = source.replace('05_prediction: one fixed quotient and pre-Ramsey threshold for all finite cube orders and selected chains',
                        '05_prediction: actual original target-cube detection tolerance chosen before the master count')
source = source.replace('Register and audit the finite-order original native prediction bridge.',
                        'Register and audit the original pre-master target-cube detection tolerance.')
ast.parse(source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules': modules, 'theorems': 4, 'definitions': 1, 'reports': 5}))
