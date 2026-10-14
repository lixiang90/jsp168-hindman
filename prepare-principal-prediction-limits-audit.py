from pathlib import Path
import ast
import json

modules = ['Hindman168/' + n + '.lean' for n in [
    'EventualUltrafilterBounds', 'FiniteProbabilityBounds', 'PrincipalModelCountBounds',
    'PrincipalPredictionLimits', 'PrincipalPredictionLimitData', 'PrincipalPredictionModelsWithLimits']]
components = [
    'A real-valued sequence that lies eventually in a compact interval on the actual ultrafilter converges to its actual canonical ultrafilter limit. The limit retains interval bounds; absolute stage errors bounded eventually by eta have limits in [0,eta]. Early terms need no global bound.',
    'Actual finite probability expectations and events lie in [0,1]. The selected block calibration probability and complete selected model color count satisfy these bounds eventually, using the proved nonnegative normalized raw harmonic law, unit-range models and every nonempty product-color mask.',
    'Selected calibration converges on the fixed ultrafilter and satisfies the exact limit bound 3 theta + cap. Complete bounded model counts converge in [0,1]. The original selected weighted count and its absolute comparison error also converge, and the limit error and difference of count limits are at most the prescribed count tolerance.',
    'PrincipalPredictionLimitData packages actual limits for all valid selected blocks and every finite principal chain. The same witnesses from principal_prediction_models now carry this data while retaining all prior admissibility, calibration, testing, weighted count and common native manifold properties. Native inverse existence remains an explicit unproved input.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional on those inverse inputs, the identical selected models now carry actual admissible parameters and fixed-ultrafilter calibration and complete weighted-versus-bounded count limits at independently prescribed tolerances chosen before N. '
    'Full Prediction integration still needs finite scale-list closure specialization and any remaining model representation details, as well as unconditional inverse inputs. '
    'Alignment and final ordered positive rapidly separated monochromatic extraction remain incomplete. No unavoidable blocker is established. '
    'A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The preceding turn checked current official eligibility rules and observed terminal success of the principal model count bounds focused Lean process. The prior complete calibration-count round was rechecked before new proof edits and its authoritative manifest copied as this baseline.',
    'Eventual bounds are taken on the same actual fixed ultrafilter, not on a substituted or truncated sequence. Compactness of the closed real interval gives actual convergence; uniqueness identifies the canonical limUnder. No global bound on early terms or assumed convergence is introduced.',
    'Finite expectation bounds use actual nonnegative mass and actual total mass one. The full model count retains all nonsingleton row factors and all nonempty product masks, including singleton masks. Each factor lies in [0,1], so their finite products and expectation do too.',
    'Calibration limits transport the retained stage inequality to a weak inequality at the limit. The arbitrary positive threshold is unchanged. Actual selected raw-law normalization supplies convergence of the event probability.',
    'A bounded model count and the eventual signed error in [-eta,eta] supply convergence of the original weighted count by addition. No independent weighted-count boundedness or convergence is assumed. Continuity of subtraction and absolute value plus uniqueness of limits identifies the absolute difference of limits with the actual absolute-error limit.',
    'The model theorem preserves exactly the retained e, parameter family, ultrafilter and native model witnesses. Its limit data is proved from their existing stage calibration, complete count estimates, actual admissible probability law and unit range. All original outputs are reproduced unchanged.',
    'The pinned paper 02_framework Prediction equations require actual fixed-ultrafilter calibration and absolute count error. These are now supplied on the established selected laws. This remains conditional on the explicit native inverse input and does not prove the paper step bound, finite scale-list specialization, Alignment or the final theorem.',
    'Six new modules contain fourteen theorems, two definitions and one Prop structure. Sixteen selected kernel reports cover all new theorems and definitions, including the structure through its construction theorem. No new resource options or proof holes are permitted. Retained proof hashes and full transitive axiom sets must be unchanged except root imports and registry.',
    remaining
]
source = Path('round-principal-calibration-count-audit.py').read_text(encoding='utf-8')
replacements = {
    '== 1269': '== 1273',
    "'baseline_hash_count': 1269": "'baseline_hash_count': 1273",
    '== 21': '== 16',
    "for values in ds.values() for kind, _ in values) == 13": "for values in ds.values() for kind, _ in values) == 14",
    "for values in ds.values() for kind, _ in values) == 8": "for values in ds.values() for kind, _ in values) == 2",
    "'theorem_count': 13, 'selected_report_count': 21": "'theorem_count': 14, 'selected_report_count': 16",
    'len(own) == 1255': 'len(own) == 1261',
    'len(actual) == 5631': 'len(actual) == 5647',
    "len({f['path'] for f in files}) == 1273": "len({f['path'] for f in files}) == 1279",
    'new_theorems=13, new_definitions=8, new_structures=0, new_instances=0, new_axiom_reports=21':
        'new_theorems=14, new_definitions=2, new_structures=1, new_instances=0, new_axiom_reports=16',
    'hindman_module_count=1255': 'hindman_module_count=1261',
    'selected_axiom_report_count=5631, source_scan_module_count=1264':
        'selected_axiom_report_count=5647, source_scan_module_count=1270',
    'new_module_count=4, new_theorem_count=13': 'new_module_count=6, new_theorem_count=14',
    'new_selected_report_count=21': 'new_selected_report_count=16',
    "reference_scope='02_framework exact weighted count and block calibration; 05_prediction complete selected-law transport'":
        "reference_scope='02_framework Prediction calibration and absolute count ultrafilter limits; 05_prediction same selected native witnesses'",
    "names = ['Hindman168.' + name for p, values in ds.items() for _, name in values]":
        "names = [('Hindman168.FiniteMass.' if p.endswith('/FiniteProbabilityBounds.lean') else 'Hindman168.') + name for p, values in ds.items() for _, name in values]",
    "names = ['Hindman168.' + n for p, ds in declarations().items() for _, n in ds]":
        "names = [('Hindman168.FiniteMass.' if p.endswith('/FiniteProbabilityBounds.lean') else 'Hindman168.') + n for p, ds in declarations().items() for _, n in ds]"
}
for before, after in reversed(list(replacements.items())):
    assert before in source, before
    source = source.replace(before, after)
values = {'PREFIX': 'round-principal-prediction-limits', 'OLD': 'round-principal-calibration-count',
    'MODULES': modules, 'COMPONENTS': components, 'REMAINING': remaining, 'EXPECTED_NEW_AXIOM_FREE': set()}
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
ast.parse(source)
anchor = "    assert names == registration['names'] and len(names) == 16\n"
statement_check = '''    prior = read('Hindman168/PrincipalPredictionModels.lean')
    assembled = read('Hindman168/PrincipalPredictionModelsWithLimits.lean')
    prior_statement = prior[prior.index('theorem principal_prediction_models'):].split(' := by\\n', 1)[0]
    assembled_statement = assembled[assembled.index('theorem principal_prediction_models_with_limits'):].split(' := by\\n', 1)[0]
    limit_field = ('          PrincipalPredictionLimitData (m := m) M e F U cap countTolerance a χ color\\n'
        '            (fun T b γ w y => (model T b γ).val w y) ∧\\n')
    assert assembled_statement.count(limit_field) == 1
    assert assembled_statement.replace(limit_field, '', 1).replace(
        'principal_prediction_models_with_limits', 'principal_prediction_models', 1) == prior_statement
'''
assert source.count(anchor) == 1
source = source.replace(anchor, anchor + statement_check, 1)
ast.parse(source)
Path('round-principal-prediction-limits-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules': 6, 'theorems': 14, 'definitions': 2, 'structures': 1,
    'reports': 16, 'baseline_hashes': 1273, 'current_modules': 1261, 'current_reports': 5647}))
