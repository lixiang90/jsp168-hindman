from pathlib import Path
import ast
import json

modules = ['Hindman168/' + n + '.lean' for n in [
    'MaskSubsetScaledForms', 'SelectedPrincipalRawLaw', 'SelectedPrincipalScales',
    'SelectedPrincipalGrowth', 'SelectedAdmissibleParameters', 'SelectedColorAdmissibleModels']]
components = [
    'The actual natural-division normalized subset sum form is proved equal to the rational form in the paper once the actual anchor divides every active coefficient. Multiplication by the anchor exactly recovers the scaled integer or natural subset sum. Positive anchor coordinates imply positive forms. Actual master column coefficients supply the positivity, divisibility and exact rational scale ratios eventually, uniformly over all subsets and integer arguments.',
    'Restriction of the full original harmonic raw product law to the selected principal indices is exactly the independent product of the original raw laws at those indices. The selected index map is injective; all discarded coordinates have actual total mass one. Exact expectation transport holds for arbitrary joint real tests, and actual selected mass nonnegativity and normalization are proved eventually.',
    'Selected subset scales are literally products of the selected original singleton master scales and equal the original master scale of their image. Positivity, powers of W, divisibility by and bounds under the actual common modulus, and the adding-block W^w divisibility all hold on these selected scales. The adding-block relation is transported by the strict principal-index embedding.',
    'The actual own padding gap dominates every fixed power of the selected earlier-cutoff auxiliary, with squared cutoffs giving a stronger bound than the paper needs. The log of the actual selected principal cutoff dominates powers of its own padding gap. This uses the proved original gap growth, actual subset product bound and original earlier-gap divisibility; no new asymptotic assumption is inserted.',
    'The same selected principal indices and the same native model witnesses now carry the proved SelectedAdmissibleFamily package, including smooth modulus powers, selected scale bounds, adding relations, own gap and cutoff growth, dyadic cutoffs and actual harmonic product probability. All retained model quality, calibration, testing, complete product-color counting and common-manifold properties are preserved. Native inverse existence is still an explicit unproved input.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional on those inverse inputs, the same selected native coloring models support both actual calibrated laws and bounded raw-coordinate count comparison at independent prescribed tolerances chosen before N. '
    'The actual selected original scales, own padding gaps, dyadic principal cutoffs and independent harmonic raw laws now satisfy the selected admissible family conditions. The original integer subset forms are proved to match the paper rational forms and to recover the actual scaled natural sums. '
    'Full Prediction output integration still needs selected-index relabeling of the complete block and count expressions and the precise ultrafilter-limit statements, as well as unconditional inverse inputs. Alignment and final ordered positive rapidly separated monochromatic extraction remain incomplete. '
    'No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The preceding bounded count sampling audit was terminal-successfully rechecked and its authoritative manifest copied before new proof edits. All retained proof sources stay unchanged.',
    'Integer and natural division are connected only after proving anchor divisibility. Rational division additionally requires actual positive anchor coefficients. The eventual master theorem obtains both facts from actual valid chain coefficients and ratios, and its rational identity uses their proved exact master scale equalities.',
    'Positive natural-coordinate normalized forms use the maximum term with coefficient c/c=1 and nonnegative remaining terms. The natural toNat sum identity explicitly proves nonnegativity before eliminating toNat. Negative integer inputs are still permitted in the separate exact rational and scaled identities.',
    'The selected principal map is injective by strict monotonicity. Restriction of piMass uses normalization of every actual unused coordinate from proved cutoff validity, rather than renormalizing or postulating selected independence. Arbitrary-test expectation equality follows from exact pushforward equality.',
    'Finite image scales are identified by the exact original product formula and an injective image product. Adding-block transport uses all strict index orders and both nonempty tails. Actual hF.adding_scales retains the original W^w factor and common modulus.',
    'Earlier selected principal indices lie before the current own padding index. Each cutoff squared is at least one, so the selected product is bounded by the full original padding auxiliary. The proof applies original gap growth to this actual bound, and uses earlier-gap divisibility to compare padding and principal gaps for cutoff growth.',
    'The selected earlier-cutoff auxiliary uses squared cutoffs; this is stronger than the paper auxiliary with first powers. SelectedAdmissibleFamily describes the exact stronger constructed conditions. The raw law is the existing actual harmonic W-unit piMass; positivity of normalizers and total mass one are proved eventually, which is the asymptotic regime used by the paper.',
    'The conditional model assembly preserves the identical e, heM, model, calibration, tests, count and common native manifold from the retained selected_color_product_counting theorem. It adds the admissibility proved from actual maskGeneratedMaster_conditions, with no replacement selection or extra parameter hypothesis.',
    'Six new modules contain twenty-two theorems, four definitions and one Prop structure. The structure and its generated projections are covered by the transitive audit of the theorem constructing it. No new resource options, axioms, sorry, admit or native_decide are allowed. Full build and registered transitive kernel reports must finish successfully without warnings. Retained hashes and axiom sets must remain unchanged except root imports and registry.',
    remaining
]
source = Path('round-bounded-count-sampling-audit.py').read_text(encoding='utf-8')
replacements = {
    '== 1251': '== 1259',
    "'baseline_hash_count': 1251": "'baseline_hash_count': 1259",
    '== 25': '== 26',
    '== 21': '== 22',
    "'theorem_count': 21, 'selected_report_count': 25": "'theorem_count': 22, 'selected_report_count': 26",
    'len(own) == 1241': 'len(own) == 1247',
    'len(actual) == 5565': 'len(actual) == 5591',
    "len({f['path'] for f in files}) == 1259": "len({f['path'] for f in files}) == 1265",
    'new_theorems=21, new_definitions=4, new_instances=0, new_axiom_reports=25':
        'new_theorems=22, new_definitions=4, new_instances=0, new_axiom_reports=26',
    'hindman_module_count=1241': 'hindman_module_count=1247',
    'selected_axiom_report_count=5565, source_scan_module_count=1250':
        'selected_axiom_report_count=5591, source_scan_module_count=1256',
    'new_module_count=8, new_theorem_count=21': 'new_module_count=6, new_theorem_count=22',
    'new_selected_report_count=25': 'new_selected_report_count=26',
    "reference_scope='05_prediction: complete bounded count sampling and prescribed tolerance on the same calibrated selected family'":
        "reference_scope='02_framework admissible parameters and normalized forms; 05_prediction same-witness selected family integration'"
}
# Replace the final hash count first so that the baseline 1251 replacement cannot touch it.
for before, after in reversed(list(replacements.items())):
    assert before in source, before
    source = source.replace(before, after)
namespace_line = "    ds[MODULES[0]] = [(kind, 'FiniteMass.' + name) for kind, name in ds[MODULES[0]]]\n"
assert source.count(namespace_line) == 1
source = source.replace(namespace_line, '', 1)
values = {'PREFIX': 'round-original-scaled-forms', 'OLD': 'round-bounded-count-sampling',
    'MODULES': modules, 'COMPONENTS': components, 'REMAINING': remaining,
    'EXPECTED_NEW_AXIOM_FREE': set()}
tree = ast.parse(source)
lines = source.splitlines(keepends=True)
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
needle = "    for section in fixed['sections']:\n"
assert source.count(needle) == 1
source = source.replace(needle, '''    framework = 'preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/build/sections/02_framework.tex'
    framework_bytes = (Path('E:/codex-build/math') / framework).read_bytes().replace(b'\\r\\n', b'\\n')
    assert not any(section['path'] == framework for section in fixed['sections'])
    fixed['sections'].append(dict(path=framework, normalized_sha256=hashlib.sha256(framework_bytes).hexdigest(), matches_pinned_git_object=True))
''' + needle, 1)
needle = 'new_theorems=22, new_definitions=4, new_instances=0, new_axiom_reports=26'
assert source.count(needle) == 1
source = source.replace(needle, 'new_theorems=22, new_definitions=4, new_structures=1, new_instances=0, new_axiom_reports=26', 1)
for node in ast.walk(ast.parse(source)):
    if isinstance(node, ast.keyword) and node.arg == 'application_review':
        old_review = ast.get_source_segment(source, node.value)
        assert source.count(old_review) == 1
        source = source.replace(old_review, repr(reviews), 1)
        break
else:
    raise AssertionError('review field missing')
ast.parse(source)
Path('round-original-scaled-forms-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules': 6, 'theorems': 22, 'definitions': 4, 'structures': 1,
    'reports': 26, 'baseline_hashes': 1259, 'current_modules': 1247, 'current_reports': 5591}))
