from pathlib import Path
import ast
import json

modules = ['Hindman168/' + n + '.lean' for n in [
    'PrincipalCoordinateChains', 'PrincipalCoordinateProducts',
    'PrincipalBoundedCounts', 'SelectedColorRelabelModels']]
components = [
    'Chains on Fin n principal coordinates lift to genuine original master chains by the actual strict principal embedding. Their tails, pivots and blocks are exactly preserved; the recovered principal tail positions and pivot coordinates equal the input finite chain. The lifted blocks lie in the selected principal set and actual master range.',
    'Each relabeled block scale coefficient is exactly the actual original master column coefficient, and each lifted global block product is literally the selected block product applied to the selected coordinates. Consequently every arbitrary joint real test of the complete block-product vector has exactly the same expectation under the original full raw law and the selected independent harmonic law, eventually.',
    'The relabeled bounded count uses the actual selected scale coefficients in every normalized nonsingleton form and retains every nonempty product mask. Both its integrand and the concrete complete product-color masks equal the original lifted expressions. Their complete expectation transports exactly to the selected independent law, allowing arbitrary stage-varying models and masks.',
    'On the identical selected native model family, every finite-coordinate chain now satisfies the complete product-color bounded count comparison under the actual selected harmonic product law at the prescribed tolerance. Tail and pivot model indices are exactly the input finite-coordinate chain. All previous actual admissibility, calibration, testing, original-chain count and common native manifold properties remain. Native inverse existence is still an explicit unproved input.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional on those inverse inputs, the same selected native models have actual admissible parameters and calibrated laws and complete product-color bounded count comparison at independently prescribed tolerances chosen before N. '
    'The full bounded count now uses relabeled finite-coordinate chains, their actual selected scale coefficients, local block products and the selected independent original harmonic raw law, with all nonempty product masks retained. '
    'Full Prediction output integration still needs exact selected block calibration and unbounded-count expression relabeling and the precise ultrafilter-limit statements, as well as unconditional inverse inputs. Alignment and final ordered positive rapidly separated monochromatic extraction remain incomplete. '
    'No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The preceding original scaled forms audit was terminal-successfully rechecked and its authoritative manifest copied before new proof edits. All retained proof sources stay unchanged.',
    'PrincipalCoordinateChain encodes the paper ordering directly on the selected Fin n coordinates. Its lift proves nonempty tails, all strict tail orders, all tails before every pivot, and strictly increasing pivots from the actual principal order embedding.',
    'The lifted block is exactly the image of the finite-coordinate block. The inverse tail filter equals the original finite tail by injectivity. Any pivot map recovered by the retained selected chain theorem is proved equal to the finite-coordinate pivots, rather than choosing a different chain or model.',
    'The relabeled coefficient is the rational floor of the actual selected subset product scale times the requested rational factor. Its equality with the original master coefficient uses the proved exact selected subset scale image identity, with no eventual floor approximation.',
    'The sample product identity converts the actual subtype product to the finite set product and then uses the injective image formula. Proof-dependent Fin M index constructors agree by proof irrelevance. No independence assumption or extra sampling error is introduced.',
    'The arbitrary-test expectation transport uses the actual original selected-coordinate piMass restriction theorem. It permits all joint tests and thus the full stage-varying integrand, not just separate coordinate tests or bounded ones.',
    'The bounded integrand preserves all nonsingleton normalized forms and all nonempty product masks, including singletons. Concrete relabeled product masks use the same exact natural coefficients; on positive natural block products they are the actual coloring indicators of the product of scaled block values.',
    'The final selected model assembly calls the retained original-chain product counting theorem on the actual lift, proves its recovered pivot and tail model indices coincide with the input finite-coordinate chain, and rewrites the exact original expectation to the selected law. The same e and all model witnesses and tolerances are preserved.',
    'Four new modules contain thirteen theorems, six definitions and one finite-chain data structure. Generated structure fields are covered by transitive theorem audits. No new resource options, axioms, sorry, admit or native_decide are allowed. Full build and kernel reports must finish without warnings. Retained proof hashes and full axiom sets must remain unchanged except root imports and registry.',
    remaining
]
source = Path('round-original-scaled-forms-audit.py').read_text(encoding='utf-8')
replacements = {
    '== 1259': '== 1265',
    "'baseline_hash_count': 1259": "'baseline_hash_count': 1265",
    '== 26': '== 19',
    '== 22': '== 13',
    "for values in ds.values() for kind, _ in values) == 4": "for values in ds.values() for kind, _ in values) == 6",
    "'theorem_count': 22, 'selected_report_count': 26": "'theorem_count': 13, 'selected_report_count': 19",
    'len(own) == 1247': 'len(own) == 1251',
    'len(actual) == 5591': 'len(actual) == 5610',
    "len({f['path'] for f in files}) == 1265": "len({f['path'] for f in files}) == 1269",
    'new_theorems=22, new_definitions=4, new_structures=1, new_instances=0, new_axiom_reports=26':
        'new_theorems=13, new_definitions=6, new_structures=1, new_instances=0, new_axiom_reports=19',
    'hindman_module_count=1247': 'hindman_module_count=1251',
    'selected_axiom_report_count=5591, source_scan_module_count=1256':
        'selected_axiom_report_count=5610, source_scan_module_count=1260',
    'new_module_count=6, new_theorem_count=22': 'new_module_count=4, new_theorem_count=13',
    'new_selected_report_count=26': 'new_selected_report_count=19',
    "reference_scope='02_framework admissible parameters and normalized forms; 05_prediction same-witness selected family integration'":
        "reference_scope='05_prediction exact principal-coordinate relabeling and complete bounded count on the selected harmonic law'"
}
for before, after in reversed(list(replacements.items())):
    assert before in source, before
    source = source.replace(before, after)
start = source.index("    framework = 'preprints/")
end = source.index("    for section in fixed['sections']:\n", start)
source = source[:start] + source[end:]
values = {'PREFIX': 'round-selected-relabel-count', 'OLD': 'round-original-scaled-forms',
    'MODULES': modules, 'COMPONENTS': components, 'REMAINING': remaining,
    'EXPECTED_NEW_AXIOM_FREE': set()}
lines = source.splitlines(keepends=True)
edits = []
for node in ast.parse(source).body:
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in values:
            edits.append((node.lineno-1, node.end_lineno, name+' = '+repr(values[name])+'\n'))
assert len(edits) == len(values)
for start, end, replacement in reversed(edits):
    lines[start:end] = [replacement]
source = ''.join(lines)
needle = '    return ds\n'
assert source.count(needle) == 1
source = source.replace(needle, '''    ds[MODULES[0]] = [(kind, 'PrincipalCoordinateChain.' + name) for kind, name in ds[MODULES[0]]]
    ds[MODULES[1]] = [(kind, name if name.startswith('MasterParameterConditions.') else 'PrincipalCoordinateChain.' + name) for kind, name in ds[MODULES[1]]]
''' + needle, 1)
for node in ast.walk(ast.parse(source)):
    if isinstance(node, ast.keyword) and node.arg == 'application_review':
        old_review = ast.get_source_segment(source, node.value)
        assert source.count(old_review) == 1
        source = source.replace(old_review, repr(reviews), 1)
        break
else:
    raise AssertionError('review field missing')
ast.parse(source)
Path('round-selected-relabel-count-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules': 4, 'theorems': 13, 'definitions': 6, 'structures': 1,
    'reports': 19, 'baseline_hashes': 1265, 'current_modules': 1251, 'current_reports': 5610}))
