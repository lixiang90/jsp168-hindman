from pathlib import Path
import ast
import re
import json

previous = 'round-mask-renamed-short-cube'
prefix = 'round-mask-block-all-gap-models'
modules = [
    'Hindman168/MaskBlockGapTemplates.lean',
    'Hindman168/MaskBlockAllGapDenseModels.lean',
    'Hindman168/MaskBlockModelChainCorrelations.lean',
    'Hindman168/MaskBlockColorDenseModels.lean',
]
components = [
    'An actual block has a proved one-column chain realization. Every permissible '
    'constant block gap belongs to a finite subtype, and every actual mask '
    'template together with the zero-prime nilsequence template satisfies the '
    'original conditions in the same canonical gap-independent master catalogue.',
    'One bounded dense model at an individual block now controls every permissible '
    'constant gap, every actual mask template and zero-prime template, and every '
    'fixed positive quotient scale. The model is chosen before the later gap '
    'and chain, using one heterogeneous finite template union and the proved '
    'countable positive-scale diagonal. Arbitrary companion stage requirements '
    'are retained without assuming the desired cube or correlation estimates.',
    'The same block model annihilates the actual rho-model endpoint cube and '
    'original subset correlation in every later chain whose tracked block '
    'has this tail and pivot, at every permissible constant gap. The original '
    'local conditioned prime law, quotient directions and harmonic root law '
    'are retained. Admissible companion factors remain arbitrary.',
    'Actual color indicators use the original masterColumnCoefficient at the '
    'block and vanish on nonpositive integers. They sum to one on positive '
    'integers; their weighted sum is exactly the actual tail divisor mask there. '
    'The coefficient is eventually positive and exactly equals the paper rational '
    'master scaling. Their actual rho weights satisfy the dense-model hypotheses, '
    'and one constructed model controls all gaps and positive quotient scales '
    'including the zero-prime native-comparison tests.'
]
reviews = [
    'PROGRESS. The previous selected F-S round was terminal-successfully rechecked, '
    'and the unchanged authoritative manifest copied before proof edits.',
    'The paper includes every permissible gap at a block before selecting coarse '
    'and fine indices. The earlier fixed-chain dense models did not by themselves '
    'supply this quantifier order. The new finite subtype includes all tail-range '
    'and gap-root compatible gaps; the original heterogeneous template union '
    'constructs one model for all of them, then the countable scale diagonal '
    'controls every fixed positive J with that same model.',
    'The one-column chain uses a nonempty tail strictly below its pivot, and '
    'its block lies in the original master range. The original block mask depends '
    'only on this tail, as proved by congruence after abstracting the dependent '
    'ordered cutoff list. The later chain and gap are quantified after model '
    'existence. The same canonical master is definitionally independent of '
    'all gap metadata.',
    'Finite template enumeration is transported by equality of the whole '
    'OriginalDualTemplate, before rewriting its dependent input arity and dimension. '
    'Direct simplification of only the projected enumeration coordinates left '
    'dependent instances unmatched. The whole-template equality gives an exact '
    'proof transport without replacing any sampling law.',
    'The target cube is paired with the actual row-template dual. Its nonroot '
    'copies of rho-model satisfy the original 1+nu majorant by the proved '
    'rho bounds and global unit model bounds. The selected all-gap dual estimate '
    'therefore proves cube convergence; the original uniform detection theorem '
    'proves the correlation bound for arbitrary admissible companion functions. '
    'No target cube smallness is an unproved premise in the constructed theorem.',
    'Color indicators use the positive natural floor of the original rational '
    'master block scaling. The retained coefficient theorem proves eventual '
    'positivity and exact rational equality. The indicators vanish on nonpositive '
    'integers and partition every positive color argument. Their actual weighted '
    'rho lies between zero and the original tail divisor mask; this follows '
    'from the proved eventual nonnegativity, not an assumed color-weight bound.',
    'All new declarations are selected for transitive kernel audit. Fresh '
    'compilations, full build and kernel audit must be terminal successful and '
    'warning-free before authoritative recording. No proof-resource options, '
    'unproved assumptions standing in for these dense-model steps, or forbidden '
    'proof operations are added.',
    'This constructs the all-gap rho-F component and actual coloring inputs. '
    'Combining these block models into the same finite Hilbert family used by '
    'selected native F-S models, completing their native comparison and the '
    'whole coloring Prediction Principle remain work. The finite-list interval '
    'inverse existence theorem is still explicitly unproved. Calibration/Alignment '
    'and final ordered positive rapidly separated monochromatic extraction '
    'remain incomplete. StrongConjecture is unproved; no unavoidable blocker '
    'or complete prize submission is claimed.'
]
source = Path(previous + '-audit.py').read_text(encoding='utf-8')
remaining = ast.literal_eval(re.search(r'^REMAINING = (.+)$', source, re.M).group(1))
marker = 'The finite-list interval inverse existence statement itself'
assert marker in remaining
remaining = remaining.replace(marker, ' '.join(components) + ' ' + marker, 1)
source = source.replace("PREFIX = '" + previous + "'", "PREFIX = '" + prefix + "'")
source = source.replace("OLD = 'round-original-short-cube-law'", "OLD = '" + previous + "'")
for name, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + name + r' = .+$', name + ' = ' + repr(value), source, count=1, flags=re.M)
numbers = {'1211': '1218', '1218': '1222', '1200': '1204', '1209': '1213', '5473': '5489'}
source = re.sub(r'\b(?:1211|1218|1200|1209|5473)\b', lambda m: numbers[m.group()], source)
source = source.replace('== 14\n', '== 16\n')
source = source.replace("for kind, _ in values) == 16", "for kind, _ in values) == 12")
source = source.replace("'theorem_count': 14, 'selected_report_count': 14", "'theorem_count': 12, 'selected_report_count': 16")
source = source.replace('new_theorems=14, new_definitions=0', 'new_theorems=12, new_definitions=4')
source = source.replace('new_axiom_reports=14', 'new_axiom_reports=16')
source = source.replace('new_module_count=7, new_theorem_count=14', 'new_module_count=4, new_theorem_count=12')
source = source.replace('new_selected_report_count=14', 'new_selected_report_count=16')
source = source.replace("    assert {n for n, v in actual.items() if not v} == old.AXIOM_FREE |", 
                        "    assert {n for n, v in actual.items() if not v} == EXPECTED_NEW_AXIOM_FREE | old.AXIOM_FREE |")
source = source.replace("OLD = '" + previous + "'", "OLD = '" + previous + "'\nEXPECTED_NEW_AXIOM_FREE = set()")
source = re.sub(r'application_review=\[.*?\], new_modules=MODULES',
                'application_review=' + repr(reviews) + ', new_modules=MODULES', source, count=1, flags=re.S)
source = source.replace('05_prediction: exact mask prime-slot transport and actual selected native F-S subset correlations',
                        '05_prediction: all-gap block dense models and actual coloring rho-F subset correlations')
source = source.replace('Register and audit the actual selected native mask-correlation bridge.',
                        'Register and audit all-gap block dense models and actual color weights.')
source = source.replace("date='2026-10-10'", "date='2026-10-11'")
source = source.replace("note = '\\n2026-10-10 '", "note = '\\n2026-10-11 '")
ast.parse(source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules': modules, 'theorems': 12, 'definitions': 4, 'reports': 16}))
