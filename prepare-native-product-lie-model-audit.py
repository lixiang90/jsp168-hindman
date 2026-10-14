from pathlib import Path
import ast
import json
import re

prefix = 'round-native-product-lie-model'
previous = 'round-alignment-array-separation'
modules = ['Hindman168/' + n + '.lean' for n in [
    'NativeProductLieAlgebra', 'NativeProductExponential',
    'NativeProductGlobalLogarithm', 'NativeProductLieSubgroup',
    'NativeProductLieModel', 'NativeProductLieTopology']]
ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|def)\s+(\w+)',
    Path(p).read_text(encoding='utf-8'), re.M) for p in modules}
assert sum(k == 'theorem' for v in ds.values() for k, _ in v) == 16
assert sum(k == 'def' for v in ds.values() for k, _ in v) == 4
assert sum(map(len, ds.values())) == 20
baseline = json.loads(Path(prefix + '-baseline.json').read_text(encoding='utf-8'))
assert baseline == json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert len(baseline['files']) == 1350
components = [
    'The native Lie algebra of the actual product of two original Lie groups is identified with the product of their original native Lie algebras. Actual smooth projection homomorphisms and their unit differentials preserve the genuine native brackets, proving the exact component comparison and the concrete Lie equivalence.',
    'The actual original exponential on the product group is the pair of the original exponentials. This is proved from the genuine differentiable projection homomorphisms and the retained invariant-flow uniqueness theorem, with no supplied exponential comparison.',
    'The product of the original simply connected nilpotent Lie groups is genuinely contractible and simply connected. Its global logarithm is exactly the pair of original global logarithms, using the proved exponential comparison and original exponential injectivity.',
    'An actual Lie subalgebra of the product of the original native Lie algebras integrates to a genuine subgroup of the original product group. Membership is exactly a pair of original exponential values at a coefficient vector in that subalgebra. For the original simply connected groups, membership is equivalently membership of the pair of original logarithms; the subgroup is closed and simply connected.',
    'The tangent-model submodule of the transported native product Lie subalgebra is exactly the original coefficient subspace in E times F. This equality is proved by the actual Lie subalgebra image membership theorem and the concrete underlying product identity.',
    'The literal pair of original exponentials is a homeomorphism from that original coefficient subspace to the integrated subgroup with its inherited topology. Its inverse is the pair of original global logarithms. Actual continuity and inverse identities prove contractibility and connectedness of the genuine subgroup. Arbitrary finite products, the full native array group and the specified array lattice remain separate obligations.'
]
remaining = baseline['last_round']['remaining'].replace(
    'Construction and identification of its native simply connected array group, array-group topology, discrete cocompact lattice and smooth quotient evaluation remain unproved.',
    'The actual binary product native Lie algebra, componentwise original exponential and global logarithm, and integration and inherited topology of every product Lie subalgebra are now proved. Extending this construction to the complete finite integer evaluation image, construction and identification of the full native simply connected array group, discrete cocompact lattice and smooth quotient evaluation remain unproved.')
assert remaining != baseline['last_round']['remaining']
reviews = [
    'PROGRESS. The preceding finite-array-separation round was authoritatively rechecked and its 1350-source manifest was copied before new proof edits. Retained proof sources and exact selected axiom sets remain fixed.',
    'The product Lie bracket comparison uses the actual original native models and smooth group projection homomorphisms. Their genuine unit differentials equal the coordinate projections. The proof does not replace the native bracket with an abstract product bracket; it proves the concrete Lie equivalence.',
    'The original exponential comparison uses actual invariant integral curves and uniqueness through the retained smooth homomorphism theorem. No exponential functoriality or BCH closure is assumed as an extra input.',
    'Simply connectedness of the product is derived from the actual original exponential homeomorphisms, which make both factors contractible, and the genuine product contractibility instance. No additional product simply-connectedness hypothesis or unconstructed model is introduced.',
    'The integrated subgroup is constructed by mapping the actual product Lie subalgebra into the native Lie algebra of the actual product group. The retained finite Picard logarithm proof supplies exponential-image subgroup closure. Literal exponential and logarithm membership descriptions, closedness and simply connectedness are proved for this same subgroup.',
    'The transported tangent-model submodule is proved equal to the original coefficient subspace. A direct homeomorphism uses the literal pair of original exponentials and logarithms, with actual inherited subtype topologies. Its inverse laws and continuity are proved directly. Convexity of the original model submodule then proves contractibility and connectedness.',
    'This binary-product construction does not assert that two evaluations determine arbitrary array coefficients. The full fixed finite evaluation image must still be integrated in an arbitrary finite original-group product. The all-integer array group identification, lattice discreteness and cocompactness, and smooth quotient evaluation are still unproved.',
    'Six new modules contain 16 theorems and four definitions, all 20 declarations selected for kernel audit. No proof holes, new axioms, structures, global instances, unsafe code or resource settings are introduced. Strict focused checks, full build, kernel checks, retained-source and exact-axiom comparisons and final recheck must terminate successfully.',
    remaining
]
source = Path(previous + '-audit.py').read_text(encoding='utf-8')
replacements = {
    "len(baseline['files']) == 1344": "len(baseline['files']) == 1350",
    "'baseline_hash_count': 1344": "'baseline_hash_count': 1350",
    'len(set(names)) == 17': 'len(set(names)) == 20',
    "for values in ds.values() for kind, _ in values) == 15": "for values in ds.values() for kind, _ in values) == 16",
    "for values in ds.values() for kind, _ in values) == 2": "for values in ds.values() for kind, _ in values) == 4",
    "'theorem_count': 15, 'selected_report_count': 17": "'theorem_count': 16, 'selected_report_count': 20",
    "names == registration['names'] and len(names) == 17": "names == registration['names'] and len(names) == 20",
    'len(own) == 1332': 'len(own) == 1338',
    'len(actual) == 6043': 'len(actual) == 6063',
    "len({f['path'] for f in files}) == 1350": "len({f['path'] for f in files}) == 1356",
    'new_theorems=15, new_definitions=2, new_structures=0, new_instances=0, new_axiom_reports=17':
        'new_theorems=16, new_definitions=4, new_structures=0, new_instances=0, new_axiom_reports=20',
    'hindman_module_count=1332': 'hindman_module_count=1338',
    'selected_axiom_report_count=6043, source_scan_module_count=1341':
        'selected_axiom_report_count=6063, source_scan_module_count=1347',
    'new_module_count=6, new_theorem_count=15': 'new_module_count=6, new_theorem_count=16',
    'new_selected_report_count=17': 'new_selected_report_count=20',
    "reference_scope='08_alignment same-step array Lie nilpotence and coefficient recovery by finitely many integer evaluations'":
        "reference_scope='08_alignment actual native product Lie model and exponential integration of the finite evaluation image'"
}
for old in replacements:
    assert old in source, old
pattern = re.compile('|'.join(re.escape(s) for s in sorted(replacements, key=len, reverse=True)))
source = pattern.sub(lambda m: replacements[m.group()], source)
values = {'PREFIX': prefix, 'OLD': previous, 'MODULES': modules,
    'COMPONENTS': components, 'REMAINING': remaining, 'EXPECTED_NEW_AXIOM_FREE': set()}
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
anchor = "    prior = read('Hindman168/PrincipalPredictionModels.lean')\n"
scope = '''    product = read('Hindman168/NativeProductLieAlgebra.lean')
    assert 'nativeSmoothHom_bracket' in product and 'mfderiv_fst' in product
    assert 'GroupLieAlgebra (I.prod J) (G × K)' in product
    exponential = read('Hindman168/NativeProductExponential.lean')
    assert 'nativeLieExponential_map' in exponential
    assert 'nativeProductExponential_eq' in exponential
    logarithm = read('Hindman168/NativeProductGlobalLogarithm.lean')
    assert 'nativeLieGroup_contractible' in logarithm
    assert 'nativeProductGroup_simplyConnected' in logarithm
    assert 'nativeLieExponential_injective' in logarithm
    subgroup = read('Hindman168/NativeProductLieSubgroup.lean')
    assert 'nativeLieSubalgebraSubgroup (I := I.prod J)' in subgroup
    assert 'nativeProductLieSubgroup_globalLogarithm_iff' in subgroup
    model = read('Hindman168/NativeProductLieModel.lean')
    assert 'Submodule ℝ (E × F) := S.toSubmodule' in model
    assert 'nativeProductLieModel_map_eq' in model
    topology = read('Hindman168/NativeProductLieTopology.lean')
    assert 'nativeProductLieModel S ≃ₜ nativeProductLieSubgroup S' in topology
    assert 'continuous_subtype_val' in topology
    assert 'V.convex.contractibleSpace' in topology
'''
assert source.count(anchor) == 1
source = source.replace(anchor, scope + anchor, 1)
ast.parse(source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
focused = Path('check-alignment-array-separation.py').read_text(encoding='utf-8')
assert focused.count("prefix = 'round-alignment-array-separation'") == 1
focused = focused.replace("prefix = 'round-alignment-array-separation'", 'prefix = ' + repr(prefix))
Path('check-native-product-lie-model.py').write_text(focused, encoding='utf-8')
print(json.dumps({'prepared_modules': len(modules), 'theorems': 16, 'definitions': 4, 'declarations': 20}))
