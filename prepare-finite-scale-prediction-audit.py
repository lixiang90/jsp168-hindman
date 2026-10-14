from pathlib import Path
import ast
import json

modules = ['Hindman168/' + n + '.lean' for n in [
    'FiniteScaleLists', 'FiniteScaleColorIndices', 'FiniteScalePredictionLimits', 'FiniteScalePredictionModels']]
components = [
    'An explicit finite positive rational enlargement of A contains every block product of every tuple in B, and retains all previous palette indices. It is constructed solely from the finite input lists, before model parameters, thresholds, coloring and ultrafilter choices.',
    'One finite scale-and-color index set contains each actual rational scale together with every color. Every column index is formed by proved membership of its actual block product. Its factor and color are exactly the requested values; no approximate coefficients or renamed colors are substituted.',
    'Actual selected-law calibration specializes to every scale in A and every color, including each block product in B. The complete chain count specializes with a column factor equal to its own block product and one common sum/product color. Model counts remain in [0,1], both counts converge on the same fixed ultrafilter, and the absolute error limit is at most eta.',
    'The native model existence theorem specializes its entire retained statement to the finite scale-and-color family. Parameters and tolerances are chosen before the master dimension and coloring, and the same selected witnesses supply all original tests, stage estimates, complete limit data and common native representation. Native inverse existence remains an explicit unproved input.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional Prediction now includes actual admissible parameters, the same selected native models, finite positive scale-list closure, all scale/color indices, and actual fixed-ultrafilter calibration and complete count limits. '
    'The common-manifold model output still needs explicitly proved [0,1] observable range on the entire quotient with uniform Lipschitz bounds; unconditional inverse inputs still need proof. '
    'Alignment, including its finite nilpotent recurrence plan and positive-probability realization, and final ordered positive rapidly separated monochromatic extraction remain incomplete. '
    'No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The preceding prediction-limits round was terminal-successfully rechecked, and its authoritative manifest copied before new source edits. All retained proof sources remain fixed.',
    'The closure enlargement is a finite biUnion over B of finite powerset images. It retains A, contains all nonempty block products and, harmlessly, empty products. Actual coordinatewise positivity proves positivity of each new rational product. The construction is independent of models, thresholds and all master parameters.',
    'ScaleColorIndex is the product of the actual finite subtype A and Fin r. Its projections and the block-product index preserve the actual rational factor and color definitionally. Membership is supplied by the proved finite closure, not by a new external assumption about the count.',
    'Calibration is specialized directly from the same PrincipalPredictionLimitData on the same ultrafilter. For chain counting, each column is indexed by b_(C.block col), and every index color is the one requested common color. The original selected weighted count, full bounded model integrand and all nonempty product-color masks are unchanged.',
    'The native existence theorem is the exact retained statement specialized to the finite scale-and-color index type and its projection functions. All original outputs are retained verbatim. The index family and tolerances are fixed before N; positivity of the finite scale list discharges the actual factor positivity premise.',
    'The paper 02_framework scale-list closure and Prediction equations now connect to the finite-family models and their actual principal laws. This does not prove a finite Alignment plan, positive-probability Alignment, external native inverse existence or StrongConjecture.',
    'Four new modules contain twelve theorems and seven definitions/abbreviations. Nineteen selected kernel reports cover every new declaration. Full build and kernel reports must finish without warnings; no new resource options, axioms or proof holes are allowed. Retained source hashes and full transitive axiom sets must remain unchanged except root imports and registry.',
    remaining
]
source = Path('round-principal-prediction-limits-audit.py').read_text(encoding='utf-8')
replacements = {
    '== 1273': '== 1279', "'baseline_hash_count': 1273": "'baseline_hash_count': 1279",
    '== 16': '== 19',
    "for values in ds.values() for kind, _ in values) == 14": "for values in ds.values() for kind, _ in values) == 12",
    "for values in ds.values() for kind, _ in values) == 2": "for values in ds.values() for kind, _ in values) == 7",
    "'theorem_count': 14, 'selected_report_count': 16": "'theorem_count': 12, 'selected_report_count': 19",
    'len(own) == 1261': 'len(own) == 1265', 'len(actual) == 5647': 'len(actual) == 5666',
    "len({f['path'] for f in files}) == 1279": "len({f['path'] for f in files}) == 1283",
    'new_theorems=14, new_definitions=2, new_structures=1, new_instances=0, new_axiom_reports=16':
        'new_theorems=12, new_definitions=7, new_structures=0, new_instances=0, new_axiom_reports=19',
    'hindman_module_count=1261': 'hindman_module_count=1265',
    'selected_axiom_report_count=5647, source_scan_module_count=1270':
        'selected_axiom_report_count=5666, source_scan_module_count=1274',
    'new_module_count=6, new_theorem_count=14': 'new_module_count=4, new_theorem_count=12',
    'new_selected_report_count=16': 'new_selected_report_count=19',
    "reference_scope='02_framework Prediction calibration and absolute count ultrafilter limits; 05_prediction same selected native witnesses'":
        "reference_scope='02_framework finite scale-list closure and Prediction; 08_alignment finite palette index requirements'",
    "('Hindman168.FiniteMass.' if p.endswith('/FiniteProbabilityBounds.lean') else 'Hindman168.')": "'Hindman168.'",
    "old.AXIOM_FREE | {'Hindman168.intervalResidueParent'":
        "{n for n, v in previous.items() if not v} | {'Hindman168.intervalResidueParent'"
}
for before, after in reversed(list(replacements.items())):
    assert before in source, before
    source = source.replace(before, after)
values = {'PREFIX': 'round-finite-scale-prediction', 'OLD': 'round-principal-prediction-limits',
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
ast.parse(source)
anchor = "    for p in own + pnt + [Path('Hindman168.lean'), Path('Verification.lean')]:\n"
extra_check = '''    finite_source = read('Hindman168/FiniteScalePredictionModels.lean')
    finite_statement = finite_source[finite_source.index('theorem finite_scale_prediction_models'):].split(' := by\\n', 1)[0]
    specialized = assembled_statement.replace(
        'theorem principal_prediction_models_with_limits (ι : Type*) [Fintype ι]',
        'theorem finite_scale_prediction_models (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a)', 1)
    specialized = re.sub(r'\\bι\\b', '(ScaleColorIndex A r)', specialized)
    old_quantifiers = ('      ∀ (a : (ScaleColorIndex A r) → ℚ) (_ha : ∀ γ, 0 < a γ)\\n'
        '        (χ : ℕ → Fin r) (color : (ScaleColorIndex A r) → Fin r),\\n')
    assert specialized.count(old_quantifiers) == 1
    specialized = specialized.replace(old_quantifiers,
        '      let a := scaleColorFactor A r\\n      let color := scaleColorValue A r\\n      ∀ χ : ℕ → Fin r,\\n', 1)
    assert finite_statement == specialized
'''
assert source.count(anchor) == 1
source = source.replace(anchor, extra_check + anchor, 1)
anchor = "    for section in fixed['sections']:\n"
extra_check = '''    alignment = 'preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/build/sections/08_alignment.tex'
    alignment_bytes = (Path('E:/codex-build/math') / alignment).read_bytes().replace(b'\\r\\n', b'\\n')
    assert alignment not in {section['path'] for section in fixed['sections']}
    fixed['sections'].append(dict(path=alignment,
        normalized_sha256=hashlib.sha256(alignment_bytes).hexdigest(), matches_pinned_git_object=True))
'''
assert source.count(anchor) == 1
source = source.replace(anchor, extra_check + anchor, 1)
ast.parse(source)
Path('round-finite-scale-prediction-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules': 4, 'theorems': 12, 'definitions': 7, 'reports': 19,
    'baseline_hashes': 1279, 'current_modules': 1265, 'current_reports': 5666}))
