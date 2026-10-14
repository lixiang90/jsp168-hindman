from pathlib import Path
import ast
import json
import re

prefix = 'round-native-finite-product-model'
previous = 'round-native-product-lie-model'
modules = ['Hindman168/' + n + '.lean' for n in [
    'NativeFiniteProductSpaces', 'NativeFiniteProductManifold',
    'NativeFiniteProductCoordinates', 'NativeFiniteProductLieMap',
    'NativeFiniteProductExponential', 'AlignmentNativeFiniteEvaluationImage',
    'AlignmentNativeFiniteImageSubgroup']]
ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|def)\s+(\w+)',
    Path(p).read_text(encoding='utf-8'), re.M) for p in modules}
assert sum(k == 'theorem' for v in ds.values() for k, _ in v) == 26
assert sum(k == 'def' for v in ds.values() for k, _ in v) == 13
assert sum(map(len, ds.values())) == 39
baseline = json.loads(Path(prefix + '-baseline.json').read_text(encoding='utf-8'))
assert baseline == json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert len(baseline['files']) == 1356
components = [
    'Nonempty finite products are genuine recursively iterated products of the original group and tangent model, with n+1 factors. Their actual group, topology, normed real vector space, completeness, finite dimension, Hausdorffness, nilpotence and connectedness structures are constructed recursively, with no global instances.',
    'The finite product has actual recursive product charts and models with corners, with the original manifold chart at every factor. The chart model retains the required ModelProd manifold tags. Its original native Lie group and boundaryless structures are proved, and actual product contractibility gives simply connectedness for the original simply connected nilpotent groups.',
    'Every actual finite product coordinate is explicitly constructed, and equality at all n+1 original coordinates determines the product. The last and prefix coordinate equations are proved for this same recursive product.',
    'A finite family of original Lie evaluation homomorphisms is assembled into a genuine Lie homomorphism to the native Lie algebra of the actual finite group product. The previously proved actual native binary product Lie equivalence is used recursively. Its original coordinates are exactly the supplied evaluations, and joint evaluation injectivity implies injectivity of this native homomorphism.',
    'Every coordinate of the actual finite product exponential is the original exponential of that original tangent coordinate. The exact original global logarithm coordinate formula follows from the actual exponential comparison and inverse laws. These formulas also hold for coefficient images under the constructed native Lie homomorphism.',
    'The entire original native polynomial-array coefficient Lie algebra embeds into the native Lie algebra of one actual finite original-group product by a fixed finite family of actual integer evaluations. The previously proved finite separation set is augmented by the zero input, genuinely enumerated by Fin(n+1), and used to prove the embedding injective. This also covers an empty original selection and a zero coefficient algebra.',
    'The full finite evaluation image integrates to a genuine subgroup of the actual finite original-group product. Every element is the actual original-product exponential of an array coefficient vector, with exactly the original integer-evaluation exponentials at each selected coordinate. For original simply connected groups this coefficient parametrization is injective and the subgroup is closed, contractible and simply connected. Compatibility at all other integer evaluations and the specified array lattice still require proofs.'
]
remaining = baseline['last_round']['remaining'].replace(
    'Extending this construction to the complete finite integer evaluation image, construction and identification of the full native simply connected array group, discrete cocompact lattice and smooth quotient evaluation remain unproved.',
    'The complete native array coefficient algebra now embeds by one fixed finite family of integer inputs into the native Lie algebra of an actual finite original-group product. Its finite evaluation image integrates to a closed contractible simply connected subgroup, uniquely parameterized by coefficient exponentials. Compatibility of reconstructed multiplication with every remaining integer evaluation, construction and identification of the full native array group, its specified discrete cocompact lattice and smooth quotient evaluation remain unproved.')
assert remaining != baseline['last_round']['remaining']
reviews = [
    'PROGRESS. The preceding binary-product round was authoritatively rechecked and its 1356-source manifest was copied before new proof edits. Retained proof sources and exact selected axiom sets remain fixed.',
    'The original finite product group, tangent model and chart model are constructed recursively. The n=0 case is one original factor, rather than an empty product; adding the zero input makes the actual selected evaluation family nonempty. All recursively constructed structures are locally installed definitions or proved propositions. No supplied finite-product Lie group or simply-connectedness premise is introduced.',
    'The chart model uses the actual ModelProd tags at every recursive step. It is not assigned a guessed chart structure on a plain function type. The actual product chart, model with corners, Lie group and boundaryless structures are checked together; contractibility of the original factors proves product simply connectedness.',
    'The finite Lie evaluation map is recursively composed through the proved native binary product Lie equivalence. Each coordinate equals the corresponding original Lie evaluation, and actual joint injectivity transfers to the native homomorphism. No point separation or bracket comparison is assumed for the array algebra.',
    'The exact original exponential formulas use the retained actual binary-product exponential theorem. The global logarithm coordinate formula uses original exponential injectivity and the actual global inverse identities. Neither BCH functoriality nor a replacement exponential is introduced.',
    'The finite evaluation selection is the retained proven fixed set. Augmentation by the zero integer input and a genuine finite equivalence enumerate it, even when the original set is empty. Every original selected evaluation is recovered through this equivalence, so the retained full coefficient separation proves injectivity for all coefficient vectors simultaneously.',
    'The finite image is an actual Lie subalgebra range in the actual finite-product native Lie algebra. The retained Picard logarithm subgroup proof integrates it. Actual range membership supplies coefficient preimages; native exponential injectivity and coefficient embedding injectivity prove their uniqueness. The same actual subgroup is closed, contractible and simply connected.',
    'This does not yet identify the finite image subgroup with all-integer arrays under pointwise multiplication. Compatibility with unselected integer evaluations still requires an argument, as do the specified lattice discreteness, cocompactness and smooth quotient maps. The main StrongConjecture, inverse input and recurrence input remain unproved.',
    'Seven new modules contain 26 theorems and 13 definitions, all 39 declarations selected for kernel audit. No proof holes, new axioms, structures, global instances, unsafe code or resource settings are introduced. Strict focused checks, full build, kernel checks, retained-source and exact-axiom comparisons and final recheck must terminate successfully.',
    remaining
]
source = Path(previous + '-audit.py').read_text(encoding='utf-8')
replacements = {
    "len(baseline['files']) == 1350": "len(baseline['files']) == 1356",
    "'baseline_hash_count': 1350": "'baseline_hash_count': 1356",
    'len(set(names)) == 20': 'len(set(names)) == 39',
    "for values in ds.values() for kind, _ in values) == 16": "for values in ds.values() for kind, _ in values) == 26",
    "for values in ds.values() for kind, _ in values) == 4": "for values in ds.values() for kind, _ in values) == 13",
    "'theorem_count': 16, 'selected_report_count': 20": "'theorem_count': 26, 'selected_report_count': 39",
    "names == registration['names'] and len(names) == 20": "names == registration['names'] and len(names) == 39",
    'len(own) == 1338': 'len(own) == 1345',
    'len(actual) == 6063': 'len(actual) == 6102',
    "len({f['path'] for f in files}) == 1356": "len({f['path'] for f in files}) == 1363",
    'new_theorems=16, new_definitions=4, new_structures=0, new_instances=0, new_axiom_reports=20':
        'new_theorems=26, new_definitions=13, new_structures=0, new_instances=0, new_axiom_reports=39',
    'hindman_module_count=1338': 'hindman_module_count=1345',
    'selected_axiom_report_count=6063, source_scan_module_count=1347':
        'selected_axiom_report_count=6102, source_scan_module_count=1354',
    'new_module_count=6, new_theorem_count=16': 'new_module_count=7, new_theorem_count=26',
    'new_selected_report_count=20': 'new_selected_report_count=39',
    "reference_scope='08_alignment actual native product Lie model and exponential integration of the finite evaluation image'":
        "reference_scope='08_alignment actual native finite product Lie group and integration of the full finite integer evaluation image'"
}
for old in replacements:
    assert old in source, old
pattern = re.compile('|'.join(re.escape(s) for s in sorted(replacements, key=len, reverse=True)))
source = pattern.sub(lambda m: replacements[m.group()], source)
values = {'PREFIX': prefix, 'OLD': previous, 'MODULES': modules,
    'COMPONENTS': components, 'REMAINING': remaining,
    'EXPECTED_NEW_AXIOM_FREE': {'Hindman168.nativeFiniteProduct', 'Hindman168.nativeFiniteProductChartModel'}}
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
scope = '''    spaces = read('Hindman168/NativeFiniteProductSpaces.lean')
    assert '| n + 1 => nativeFiniteProduct X n × X' in spaces
    assert 'nativeFiniteProductIsNilpotent' in spaces
    manifold = read('Hindman168/NativeFiniteProductManifold.lean')
    assert 'ModelProd (nativeFiniteProductChartModel X n) X' in manifold
    assert 'nativeFiniteProductCorners I n' in manifold
    assert 'nativeLieGroup_contractible' in manifold
    coordinates = read('Hindman168/NativeFiniteProductCoordinates.lean')
    assert 'Fin.lastCases' in coordinates
    assert 'nativeFiniteProductCoordinate_injective' in coordinates
    maps = read('Hindman168/NativeFiniteProductLieMap.lean')
    assert 'nativeProductLieEquiv' in maps and '.symm.toLieHom.comp' in maps
    assert 'nativeFiniteProductLieMap_injective' in maps
    exponential = read('Hindman168/NativeFiniteProductExponential.lean')
    assert 'nativeProductExponential_fst' in exponential
    assert 'nativeFiniteProductGlobalLogarithm_coordinate' in exponential
    embedding = read('Hindman168/AlignmentNativeFiniteEvaluationImage.lean')
    assert 'alignmentNativeLieArray_finite_integer_embedding' in embedding
    assert 'insert 0 S' in embedding and 'Fintype.equivFin T' in embedding
    assert 'nativeFiniteProductLieMap_injective' in embedding
    image = read('Hindman168/AlignmentNativeFiniteImageSubgroup.lean')
    assert 'nativeLieSubalgebraSubgroup (I := nativeFiniteProductCorners I n)' in image
    assert 'LieHom.mem_range' in image
    assert 'alignmentNativeFiniteImage_exists' in image
'''
assert source.count(anchor) == 1
source = source.replace(anchor, scope + anchor, 1)
ast.parse(source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
focused = Path('check-native-product-lie-model.py').read_text(encoding='utf-8')
assert focused.count("prefix = 'round-native-product-lie-model'") == 1
focused = focused.replace("prefix = 'round-native-product-lie-model'", 'prefix = ' + repr(prefix))
Path('check-native-finite-product-model.py').write_text(focused, encoding='utf-8')
print(json.dumps({'prepared_modules': len(modules), 'theorems': 26, 'definitions': 13, 'declarations': 39}))
