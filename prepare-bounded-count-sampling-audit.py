from pathlib import Path
import ast
import json

modules = ['Hindman168/' + n + '.lean' for n in [
    'FiniteProductDensityLaw', 'OriginalChainWeightedSampling', 'SubsetSingletonFactors',
    'MaskBoundedCountSampling', 'SelectedColorRawCounting', 'SelectedColorPredictionTolerance',
    'MaskColorProductMasks', 'SelectedColorProductCounting']]
components = [
    'Finite signed product comparison masses are exactly their original pivot product mass times the product of their actual divisor densities. The proved expectation identity keeps all coefficients and does not renormalize the comparison mass.',
    'For actual valid master chains, the full raw-coordinate product statistics approximate the original weighted pivot product law uniformly over every joint real test bounded by one. This follows from the retained actual list-valued joint L1 comparison by the injectivity of List.ofFn and exact coordinatewise integer pushforward.',
    'Every small nonempty subset is its singleton maximum. With actual positive natural coefficients its normalized integer sum form is exactly that coordinate. The product of all singleton rows is therefore precisely the original product of center divisor weights, with no singleton color mask removed.',
    'The original model subset correlation is exactly the weighted original pivot expectation of the bounded nonsingleton model integrand and complete product mask. Its bound one is proved from the actual model unit bounds and all nonempty-subset mask unit bounds. Uniform joint sampling transport applies to the full integrand, even for stage-varying masks and model inputs.',
    'The same selected native model family now satisfies original unbounded color-count versus complete original raw-coordinate bounded-model-count comparison, while retaining both calibrated laws, native testing, all original subset correlations and one common native manifold. The earlier replacement estimate is applied to the actual center-and-color row family after proving its admissibility from actual divisor and color-weight bounds.',
    'The count replacement accuracy is countTolerance divided by twice the number of nonsingleton terms plus two. It is positive and its total replacement budget equals countTolerance/2. Choosing this accuracy before N and using sampling slack countTolerance/2 yields a strict eventual counting error below the prescribed countTolerance on the same calibrated models.',
    'The actual product-color mask evaluates the color of the product of all original natural master coefficients times the product argument for each nonempty column subset. It includes singleton subsets. On positive natural coordinate products it is exactly the indicator of the product of the scaled coordinates having the chosen color. The same selected family has the prescribed raw count comparison with these concrete masks.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional on those inverse inputs, the same actual selected coloring model family now supports calibration under original block-product and complete raw-coordinate laws and full raw-coordinate bounded count comparison at prescribed independent tolerances, including the concrete complete product-color masks. Both approximation tolerances are chosen before the master index count N. '
    'The former missing final bounded joint sampling count replacement is resolved in the new route. '
    'The full Prediction Principle still needs unconditional inverse inputs and admissible parameter, selected-index relabeling, exact paper scale/form and ultrafilter-limit output integration. Alignment and final ordered positive rapidly separated monochromatic extraction remain incomplete. '
    'No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The preceding capped calibration audit was terminal-successfully rechecked and its authoritative manifest copied before new proof edits. All retained proof sources must stay unchanged.',
    'The finite product density identity proves support inclusion from the actual pointwise mass identity, expands both expectations over the original support and retains all factors. It permits signed masses and arbitrary tests; no normalization assumption is used.',
    'The actual natural coordinate L1 error equals the retained actual list-valued error because List.ofFn is injective. Taking the constant sampling budget one in the proved master rapid estimate yields convergence to zero. The unit test bound is genuinely uniform at the stage; model and product mask inputs can vary with w.',
    'Coordinatewise casting to integers is the proved piMass_map pushforward. The integer comparison component is exactly the original harmonic pivot mass times its integer divisor mask on all integers, including negative arguments. No abstract law equality or extra error assumption replaces the actual construction.',
    'The singleton product is identified by an explicit equivalence from small nonempty subsets to their maximum coordinate. The positive coefficient condition is essential to the c/c=1 identity and is derived eventually from actual MasterParameterConditions.column_coefficients with the finite image of the positive scale family.',
    'The original subset product is split into its exact singleton divisor product and nonsingleton model product. All nonempty product-mask factors, including singleton masks, remain. The full model integrand is proved bounded by one, so the actual joint sampling theorem applies even though the retained center weights are unbounded.',
    'The concrete center-and-color family is proved admissible from actual nonnegative divisor masks and color weights bounded by the corresponding original divisor mask. The previously proved rho-S replacement theorem is called on that specific family and on the same selected S witnesses, then the proved bounded count sampling theorem is applied.',
    'The count accuracy countTolerance/(2*(L+1)) is chosen before N and proved positive; field algebra proves (L+1)*accuracy=countTolerance/2. The remaining sampling slack is the other half. Calibration cap and count tolerance are prescribed independently before N, while the final stage may depend on the fixed count and event parameters.',
    'The complete product-color mask uses all nonempty subsets and the original natural coefficients. The positive-natural-coordinate identity uses exact finite product multiplication, not an assumed replacement of rational scaling. General selected counting is specialized to these concrete masks using their proved unit bounds.',
    'Eight new modules contain twenty-one theorems and four definitions. No new resource options, axioms, sorry, admit or native_decide are allowed. Full build and registered transitive kernel reports must finish successfully without warnings. All retained proof hashes and axiom sets must remain unchanged, except root imports and the axiom registry.',
    remaining
]
source = Path('round-calibration-tolerance-cap-audit.py').read_text(encoding='utf-8')
replacements = {
    "assert len(baseline['files']) == 1242": "assert len(baseline['files']) == 1251",
    'assert len(names) == len(set(names)) == 10': 'assert len(names) == len(set(names)) == 25',
    "for values in ds.values() for kind, _ in values) == 10": "for values in ds.values() for kind, _ in values) == 21",
    "'baseline_hash_count': 1242": "'baseline_hash_count': 1251",
    "'theorem_count': 10, 'selected_report_count': 10": "'theorem_count': 21, 'selected_report_count': 25",
    'assert len(own) == 1233 and len(pnt) == 9': 'assert len(own) == 1241 and len(pnt) == 9',
    "assert names == registration['names'] and len(names) == 10": "assert names == registration['names'] and len(names) == 25",
    'len(actual) == 5540': 'len(actual) == 5565',
    "len({f['path'] for f in files}) == 1251": "len({f['path'] for f in files}) == 1259",
    'new_theorems=10, new_definitions=0, new_instances=0, new_axiom_reports=10':
        'new_theorems=21, new_definitions=4, new_instances=0, new_axiom_reports=25',
    'hindman_module_count=1233': 'hindman_module_count=1241',
    'selected_axiom_report_count=5540, source_scan_module_count=1242':
        'selected_axiom_report_count=5565, source_scan_module_count=1250',
    'new_module_count=9, new_theorem_count=10': 'new_module_count=8, new_theorem_count=21',
    'new_selected_report_count=10': 'new_selected_report_count=25',
    "reference_scope='05_prediction: capped tolerance chosen before N and exact global raw-coordinate calibration'":
        "reference_scope='05_prediction: complete bounded count sampling and prescribed tolerance on the same calibrated selected family'"
}
for before, after in replacements.items():
    assert source.count(before) == 1, before
    source = source.replace(before, after, 1)
tree = ast.parse(source)
lines = source.splitlines(keepends=True)
values = {'PREFIX':'round-bounded-count-sampling', 'OLD':'round-calibration-tolerance-cap',
    'MODULES':modules, 'COMPONENTS':components, 'REMAINING':remaining,
    'EXPECTED_NEW_AXIOM_FREE':set()}
edits = []
for node in tree.body:
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in values:
            edits.append((node.lineno-1, node.end_lineno, name+' = '+repr(values[name])+'\n'))
assert len(edits) == len(values)
for start, end, replacement in reversed(edits):
    lines[start:end] = [replacement]
source = ''.join(lines)
tree = ast.parse(source)
for node in ast.walk(tree):
    if isinstance(node, ast.keyword) and node.arg == 'application_review':
        old_review = ast.get_source_segment(source, node.value)
        assert source.count(old_review) == 1
        source = source.replace(old_review, repr(reviews), 1)
        break
else:
    raise AssertionError('review field missing')
ast.parse(source)
needle = "    return {p: re.findall(r'^\\s*(?:noncomputable\\s+)?(theorem|lemma|def|abbrev|instance)\\s+([A-Za-z][A-Za-z0-9_\\.]*)', old.lean_code(read(p)), re.M) for p in MODULES}"
assert source.count(needle) == 1
source = source.replace(needle,
    "    ds = {p: re.findall(r'^\\s*(?:noncomputable\\s+)?(theorem|lemma|def|abbrev|instance)\\s+([A-Za-z][A-Za-z0-9_\\.]*)', old.lean_code(read(p)), re.M) for p in MODULES}\n" +
    "    ds[MODULES[0]] = [(kind, 'FiniteMass.' + name) for kind, name in ds[MODULES[0]]]\n" +
    "    return ds", 1)
needle = "    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 21\n"
assert source.count(needle) == 1
source = source.replace(needle, needle +
    "    assert sum(kind in {'def', 'abbrev'} for values in ds.values() for kind, _ in values) == 4\n" +
    "    assert not any(kind == 'instance' for values in ds.values() for kind, _ in values)\n", 1)
needle = '        root_imports_exact=True, registered_kernel_names_exact=True, full_target_proved=False)'
assert source.count(needle) == 1
source = source.replace(needle,
    "        root_imports_exact=True, registered_kernel_names_exact=True,\n" +
    "        axiom_free_reports=sorted(n for n, v in actual.items() if not v),\n" +
    "        new_axiom_free_reports=sorted(EXPECTED_NEW_AXIOM_FREE), full_target_proved=False)", 1)
ast.parse(source)
Path('round-bounded-count-sampling-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules':8, 'new_theorems':21, 'new_definitions':4,
    'new_reports':25, 'baseline_hashes':1251, 'current_modules':1241, 'reports':5565}))
