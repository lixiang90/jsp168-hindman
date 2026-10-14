from pathlib import Path
import ast
import json

modules = ['Hindman168/NativeUnitObservables.lean', 'Hindman168/FiniteScaleNativeUnitModels.lean']
components = [
    'Unit-interval clipping does not increase the absolute value of an observable. For a piecewise model already valued in [0,1], clipping every representing observable on its entire quotient leaves the exact model function unchanged, retains its quotient, translations and initial elements, and preserves both the original supremum bound and Lipschitz constant.',
    'Any native unit-range piecewise model has an actual globally [0,1]-valued observable representation on the same native nilmanifold, with a uniform Lipschitz constant over every stage and piece.',
    'The finite-scale native Prediction family now explicitly carries globally [0,1]-valued observables on the same common native quotient, with the same original uniform B and Lip. The parameter witnesses, selected models, actual laws, full calibration/count estimates and ultrafilter limits are unchanged. Native inverse existence remains an explicit unproved input.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional Prediction now includes actual admissible parameters, finite positive scale-list closure, all scale/color indices, globally [0,1]-valued observables on a common native quotient with uniform bounds, and actual fixed-ultrafilter calibration and complete count limits. '
    'Alignment, including its finite nilpotent recurrence plan and positive-probability realization, and final ordered positive rapidly separated monochromatic extraction remain incomplete. '
    'No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The finite-scale Prediction round was terminal-successfully rechecked and its authoritative manifest copied before these new proof edits. All retained proof sources remain unchanged.',
    'The paper 02_framework piecewise-model definition explicitly requires representing observables to take values in [0,1] on their entire nilmanifolds. Prior output supplied unit-range model values and common globally bounded observables, without exposing this entire-quotient range property. This round proves and adds that exact output.',
    'The clipping function max(0,min(1,t)) is 1-Lipschitz and vanishes at zero, hence its absolute value is at most |t|. The original supremum bound B is retained even when B is smaller than one. No weaker new bound is substituted.',
    'Clipping composed with every continuous observable has the same Lipschitz constant. At every integer sample its value is unchanged because the actual model is already in [0,1]. The exact piecewise representation equality is proved, not assumed.',
    'The common model theorem keeps the same e, model, parameter family, ultrafilter, native quotient G, B and Lip. Only the observables are clipped; g, x and every own interval/residue partition are retained. All earlier outputs are reproduced exactly. The added unit range holds for every point on the quotient, every stage, every piece and every model index.',
    'Two new modules contain four theorems and no definitions or instances. Four new kernel reports must finish with standard axioms only. Full build and kernel logs must be warning-free, retained proof hashes and full transitive axiom sets must be unchanged, and the new model statement must differ only by the added observable range field.',
    remaining
]
source = Path('round-finite-scale-prediction-audit.py').read_text(encoding='utf-8')
start = source.index("    alignment = 'preprints/")
end = source.index("    for section in fixed['sections']:\n", start)
source = source[:start] + source[end:]
replacements = {
    '== 1279': '== 1283', "'baseline_hash_count': 1279": "'baseline_hash_count': 1283",
    '== 19': '== 4',
    "for values in ds.values() for kind, _ in values) == 12": "for values in ds.values() for kind, _ in values) == 4",
    "for values in ds.values() for kind, _ in values) == 7": "for values in ds.values() for kind, _ in values) == 0",
    "'theorem_count': 12, 'selected_report_count': 19": "'theorem_count': 4, 'selected_report_count': 4",
    'len(own) == 1265': 'len(own) == 1267', 'len(actual) == 5666': 'len(actual) == 5670',
    "len({f['path'] for f in files}) == 1283": "len({f['path'] for f in files}) == 1285",
    'new_theorems=12, new_definitions=7, new_structures=0, new_instances=0, new_axiom_reports=19':
        'new_theorems=4, new_definitions=0, new_structures=0, new_instances=0, new_axiom_reports=4',
    'hindman_module_count=1265': 'hindman_module_count=1267',
    'selected_axiom_report_count=5666, source_scan_module_count=1274':
        'selected_axiom_report_count=5670, source_scan_module_count=1276',
    'new_module_count=4, new_theorem_count=12': 'new_module_count=2, new_theorem_count=4',
    'new_selected_report_count=19': 'new_selected_report_count=4',
    "reference_scope='02_framework finite scale-list closure and Prediction; 08_alignment finite palette index requirements'":
        "reference_scope='02_framework piecewise-model globally unit-range observables and Prediction output'"
}
for before, after in reversed(list(replacements.items())):
    assert before in source, before
    source = source.replace(before, after)
values = {'PREFIX': 'round-native-unit-observables', 'OLD': 'round-finite-scale-prediction',
    'MODULES': modules, 'COMPONENTS': components, 'REMAINING': remaining,
    'EXPECTED_NEW_AXIOM_FREE': set()}
lines = source.splitlines(keepends=True)
edits = []
for node in ast.parse(source).body:
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in values:
            edits.append((node.lineno-1, node.end_lineno, name + ' = ' + repr(values[name]) + '\n'))
assert len(edits) == len(values)
for start, end, replacement in reversed(edits):
    lines[start:end] = [replacement]
source = ''.join(lines)
for node in ast.walk(ast.parse(source)):
    if isinstance(node, ast.keyword) and node.arg == 'application_review':
        original = ast.get_source_segment(source, node.value)
        assert source.count(original) == 1
        source = source.replace(original, repr(reviews), 1)
        break
else:
    raise AssertionError('review field missing')
anchor = "    for p in own + pnt + [Path('Hindman168.lean'), Path('Verification.lean')]:\n"
extra_check = '''    unit_source = read('Hindman168/FiniteScaleNativeUnitModels.lean')
    unit_statement = unit_source[unit_source.index('theorem finite_scale_prediction_models_unit_observables'):].split(' := by\\n', 1)[0]
    unit_field = '                (∀ w p z, 0 ≤ obs w p z ∧ obs w p z ≤ 1) ∧\\n'
    assert unit_statement.count(unit_field) == 1
    assert unit_statement.replace(unit_field, '', 1).replace(
        'finite_scale_prediction_models_unit_observables', 'finite_scale_prediction_models', 1) == finite_statement
'''
assert source.count(anchor) == 1
source = source.replace(anchor, extra_check + anchor, 1)
ast.parse(source)
Path('round-native-unit-observables-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules': 2, 'theorems': 4, 'reports': 4,
    'baseline_hashes': 1283, 'current_modules': 1267, 'current_reports': 5670}))
