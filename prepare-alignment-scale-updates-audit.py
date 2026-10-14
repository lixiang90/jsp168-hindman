from pathlib import Path
import ast
import json

modules = ['Hindman168/' + n + '.lean' for n in [
    'AlignmentBinaryWeights', 'AlignmentScaleUpdates', 'AlignmentAddingPairs',
    'AlignmentWordInflation', 'AlignmentFiniteDenominators']]
components = [
    'The exact binary subset weights on Fin n match the retained reflected binaryWeight. An earlier member strictly dominates every later subset. Actual ordered Alignment pairs P<C<{j}<{i} therefore have strictly positive inflation exponents for every update tail, including tails different from their target tail.',
    'The actual positive rational compensating update uses integer powers k^(p_l) before its pivot and k^(-p_T) at the pivot. All updated scales stay positive, the targeted block product is exactly fixed, and every ordered pair ratio changes by its exact positive k-power. All identities are on the actual finite block products.',
    'Ordered group words inflate exactly from new scales to old scales. Explicit predecessor leading and word lists protect previously obtained palette equalities: both the chosen jump J and each inflated word followed by J are included. Preservation is proved for arbitrary group actions, with no commutativity or requirement that J fix earlier targets.',
    'One positive common integer clears all rational letter exponents for every prescribed finite scale and letter family. On these exponents floor interpretation equals the exact integer power and signed coefficients give inverses. An inflated integral letter is the old-scale generator to k raised to its positive natural degree, and the entire inflated word is identity at k=0.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional Prediction includes actual admissible parameters, finite positive scale-list closure, all scale/color indices, globally unit-range common native observables and actual fixed-ultrafilter calibration and complete count limits. '
    'Alignment now has actual compensating updates, positive pair exponents, exact ordered word inflation, predecessor palette preservation, common finite denominator clearing and positive-degree integral word interpretation. '
    'The finite nilpotent polynomial recurrence alternatives, their backward/forward finite plan assembly, and positive-probability Alignment realization remain unproved. '
    'Final ordered positive rapidly separated monochromatic extraction is also incomplete. No unavoidable blocker is established. '
    'A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The previous native-unit-observables round was terminal-successfully rechecked and its authoritative manifest copied before new source edits. All retained proof sources remain fixed.',
    'The paper 08_alignment update and exponent equations are implemented on the actual principal Fin n indices. One-based index j corresponds to zero-based j-1, giving 2^(n-1-j.val). Injective reflection supplies the retained binary separation theorem; no weight approximation is introduced.',
    'AlignmentAddingPair records precisely nonempty P and C with P<C<{j}<{i}. Strict weight domination proves lambda=p_A-p_C+p_T is positive for every update tail T, not just C=T. The ratio theorem retains the actual source and target block products.',
    'The scale update uses genuine rational integer powers, including its negative pivot power. k is positive for every actual update. Finite products give the exact own-target invariance and ratio transformation, and all coordinates remain positive when the input scales are positive.',
    'Word evaluation is an ordered product with signed rational letter coefficients. The rational scalar is preserved exactly by inflation before any floor operation. Finite denominator clearing subsequently proves those exponents integral; exact integral-value and signed-inverse theorems prevent a rounded interpretation from being mistaken for the paper letters.',
    'At a new center Jx, preservation compares both Jx and I_k(w)Jx with the same old center and same actual palette index. The group action identity (wJ)x=w(Jx) fixes the handedness. No commutativity, commutator cancellation or fixing of old targets is used.',
    'The finite predecessor lists are explicit images and an insertion of J. Their membership discharges every preservation budget. A common denominator exists for the actual finite scale-letter product set, before stage or model choices.',
    'Positive lambda has an exact natural degree. Under proved integral old-scale exponents, inflated letters are powers of their actual old-scale generators with exponent k^degree. The inflated word equals identity at zero, matching a required polynomial recurrence hypothesis. No nilpotent recurrence existence or finite subcover conclusion is assumed or claimed.',
    'Five new modules contain twenty-three theorems, twelve definitions and one pair structure. Thirty-five selected reports cover all theorems and definitions. Full build and kernel logs must finish warning-free; new resource options, axioms and proof holes are forbidden. Retained source hashes and full transitive axiom sets must stay unchanged except root imports and registry.',
    remaining
]
source = Path('round-native-unit-observables-audit.py').read_text(encoding='utf-8')
replacements = {
    '== 1283': '== 1285', "'baseline_hash_count': 1283": "'baseline_hash_count': 1285",
    'len(set(names)) == 4': 'len(set(names)) == 35',
    "for values in ds.values() for kind, _ in values) == 4": "for values in ds.values() for kind, _ in values) == 23",
    "for values in ds.values() for kind, _ in values) == 0": "for values in ds.values() for kind, _ in values) == 12",
    "'theorem_count': 4, 'selected_report_count': 4": "'theorem_count': 23, 'selected_report_count': 35",
    'names == registration[\'names\'] and len(names) == 4': 'names == registration[\'names\'] and len(names) == 35',
    'len(own) == 1267': 'len(own) == 1272', 'len(actual) == 5670': 'len(actual) == 5705',
    "len({f['path'] for f in files}) == 1285": "len({f['path'] for f in files}) == 1290",
    'new_theorems=4, new_definitions=0, new_structures=0, new_instances=0, new_axiom_reports=4':
        'new_theorems=23, new_definitions=12, new_structures=1, new_instances=0, new_axiom_reports=35',
    'hindman_module_count=1267': 'hindman_module_count=1272',
    'selected_axiom_report_count=5670, source_scan_module_count=1276':
        'selected_axiom_report_count=5705, source_scan_module_count=1281',
    'new_module_count=2, new_theorem_count=4': 'new_module_count=5, new_theorem_count=23',
    'new_selected_report_count=4': 'new_selected_report_count=35',
    "reference_scope='02_framework piecewise-model globally unit-range observables and Prediction output'":
        "reference_scope='08_alignment exact scale updates, positive exponents, ordered word inflation, predecessor requirements and finite denominator clearing'"
}
for before, after in reversed(list(replacements.items())):
    assert before in source, before
    source = source.replace(before, after)
values = {'PREFIX': 'round-alignment-scale-updates', 'OLD': 'round-native-unit-observables',
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
anchor = "    assert not any(kind == 'instance' for values in ds.values() for kind, _ in values)\n"
assert source.count(anchor) == 1
source = source.replace(anchor, anchor +
    "    assert sum(len(re.findall(r'^\\s*structure\\s+', old.lean_code(read(p)), re.M)) for p in MODULES) == 1\n", 1)
ast.parse(source)
Path('round-alignment-scale-updates-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules': 5, 'theorems': 23, 'definitions': 12, 'structures': 1,
    'reports': 35, 'baseline_hashes': 1285, 'current_modules': 1272, 'current_reports': 5705}))
