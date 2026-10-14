from pathlib import Path
import ast
import json

modules = ['Hindman168/' + n + '.lean' for n in [
    'PrincipalSubsetProductLaws', 'PrincipalBlockCalibration',
    'PrincipalWeightedColorCounts', 'PrincipalPredictionModels']]
components = [
    'The actual finite selected tail product law equals the original tailMass through an explicit equivalence between a finite subset and its principal image. The equality holds without normalization assumptions. Selected subset products also equal the original image-coordinate products exactly.',
    'The color coefficient of a selected block is the rational floor of its actual selected subset scale times the requested factor, exactly equal to the original coefficient. Sampling that finite block under the selected independent harmonic mass gives the actual original block-product law for every test and event, eventually. Unused coordinates disappear by their proved actual total mass one.',
    'The relabeled weighted count is written with the actual selected pivot product laws, independent tail-product divisor weights, singleton center weights, all nonsingleton weighted color rows and all nonempty product-color masks. Each weight and the full count equal their original lifted expressions, with coefficient positivity supplied eventually by actual master conditions.',
    'The identical selected native model family now has block calibration under the selected independent raw harmonic law and complete actual selected weighted-versus-bounded color counting at the prescribed independent tolerances. All prior admissibility, original laws, testing, finite-coordinate count and common-manifold properties are preserved. Native inverse existence remains an explicit unproved input.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional on those inverse inputs, the same selected native models have actual admissible parameters, actual selected block calibration and complete selected weighted-versus-bounded color count at independently prescribed tolerances chosen before N. '
    'The relabeled raw harmonic product law, tail-product divisor law, pivot product law, coefficients, normalized forms, singleton center weights and all nonempty product-color masks are now connected by exact proved identities. '
    'Full Prediction output integration still needs the precise ultrafilter-limit statements, finite scale-list closure specialization and any remaining model representation details, as well as unconditional inverse inputs. Alignment and final ordered positive rapidly separated monochromatic extraction remain incomplete. '
    'No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The preceding selected relabel count audit was terminal-successfully rechecked and its authoritative manifest copied before new proof edits. All retained proof sources stay unchanged.',
    'The subset-image equivalence uses injectivity of the genuine principal order embedding and surjectivity from actual finite-image membership. The full tail-law equality follows by piMass reindexing and equality of finite products, then by the retained raw-product law for the actual increasing enumeration. No normalization or independence input is added to this identity.',
    'Subset and one-block sample identities convert dependent subtype products to ordinary finite-set products before image rewriting. This preserves the actual master-coordinate Fin M indices and avoids silently changing dependent enumeration instances. The block tail is nonempty and strictly before its pivot.',
    'Block calibration uses exact selected-coordinate expectation transport and the retained actual original block-product event law. The arbitrary event is transported at each sufficiently late stage. The selected block coefficient equals the actual original rational floor, so there is no assumed rounding replacement or changed color argument.',
    'The selected divisor weight is built from the actual independent tail-product pushforward, not an abstract equivalent density. The pivot law remains the exact original harmonic integer piMass. The mask-generated master is independent of gap metadata, so the same actual family is used for both chain and original block weights.',
    'The weighted count is the expectation of all singleton center divisor factors times the full nonsingleton weighted-color integrand and complete product mask. The original correlation equality uses the retained singleton factor theorem and actual eventual coefficient positivity. No unbounded factor is dropped or bounded-test approximation substituted for an exact identity.',
    'The final assembly keeps exactly the e, model and parameter witnesses from selected_color_relabel_models. Its new local block calibration rewrites the retained original product calibration; its new full local weighted comparison rewrites the retained original correlation by the proved weighted count identity. All calibration and counting tolerances remain chosen before N.',
    'Four new modules contain thirteen theorems and eight definitions. No new resource options, axioms, sorry, admit or native_decide are allowed. Full build and kernel reports must finish without warnings. Retained proof hashes and full axiom sets must remain unchanged except root imports and registry.',
    remaining
]
source = Path('round-selected-relabel-count-audit.py').read_text(encoding='utf-8')
replacements = {
    '== 1265': '== 1269',
    "'baseline_hash_count': 1265": "'baseline_hash_count': 1269",
    '== 19': '== 21',
    "for values in ds.values() for kind, _ in values) == 6": "for values in ds.values() for kind, _ in values) == 8",
    "'theorem_count': 13, 'selected_report_count': 19": "'theorem_count': 13, 'selected_report_count': 21",
    'len(own) == 1251': 'len(own) == 1255',
    'len(actual) == 5610': 'len(actual) == 5631',
    "len({f['path'] for f in files}) == 1269": "len({f['path'] for f in files}) == 1273",
    'new_theorems=13, new_definitions=6, new_structures=1, new_instances=0, new_axiom_reports=19':
        'new_theorems=13, new_definitions=8, new_structures=0, new_instances=0, new_axiom_reports=21',
    'hindman_module_count=1251': 'hindman_module_count=1255',
    'selected_axiom_report_count=5610, source_scan_module_count=1260':
        'selected_axiom_report_count=5631, source_scan_module_count=1264',
    'new_selected_report_count=19': 'new_selected_report_count=21',
    "reference_scope='05_prediction exact principal-coordinate relabeling and complete bounded count on the selected harmonic law'":
        "reference_scope='02_framework exact weighted count and block calibration; 05_prediction complete selected-law transport'"
}
for before, after in reversed(list(replacements.items())):
    assert before in source, before
    source = source.replace(before, after)
source = '\n'.join(line for line in source.split('\n') if not line.startswith('    ds[MODULES['))
values = {'PREFIX': 'round-principal-calibration-count', 'OLD': 'round-selected-relabel-count',
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
for node in ast.walk(ast.parse(source)):
    if isinstance(node, ast.keyword) and node.arg == 'application_review':
        old_review = ast.get_source_segment(source, node.value)
        assert source.count(old_review) == 1
        source = source.replace(old_review, repr(reviews), 1)
        break
else:
    raise AssertionError('review field missing')
ast.parse(source)
Path('round-principal-calibration-count-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules': 4, 'theorems': 13, 'definitions': 8,
    'reports': 21, 'baseline_hashes': 1269, 'current_modules': 1255, 'current_reports': 5631}))
