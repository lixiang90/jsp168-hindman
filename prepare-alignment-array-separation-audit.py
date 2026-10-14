from pathlib import Path
import ast
import json
import re

prefix = 'round-alignment-array-separation'
previous = 'round-alignment-graded-lie-arrays'
modules = ['Hindman168/' + n + '.lean' for n in [
    'AlignmentLieTensorLayers', 'AlignmentLieArrayNilpotence',
    'AlignmentLieArrayIntegerSeparation', 'AlignmentFiniteEvaluationSelection',
    'AlignmentLieArrayFiniteEmbedding', 'AlignmentNativeLieArrayFiniteEvaluations']]
ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|def)\s+(\w+)',
    Path(p).read_text(encoding='utf-8'), re.M) for p in modules}
assert sum(k == 'theorem' for v in ds.values() for k, _ in v) == 15
assert sum(k == 'def' for v in ds.values() for k, _ in v) == 2
assert sum(map(len, ds.values())) == 17
baseline = json.loads(Path(prefix + '-baseline.json').read_text(encoding='utf-8'))
assert baseline == json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert len(baseline['files']) == 1344
components = [
    'The full scalar-extension Lie algebra has genuine coefficient layers spanned by p tensor x with x in original Lie lower-central layer k. Bracketing by any ambient polynomial tensor lowers the layer to k+1. Actual span and tensor inductions give its original lower-central inclusion and termination at the original Lie-algebra cutoff, without finite dimension or evaluation injectivity assumptions.',
    'The graded polynomial-array Lie algebra inherits the same lower-central cutoff through its actual injective inclusion in the scalar extension. Its nilpotence and the native coefficient-array cutoff at Group.nilpotencyClass are proved from the original native group-to-Lie cutoff.',
    'Actual integer evaluations separate the coefficient tensors over characteristic-zero fields. A basis of the original Lie algebra extracts genuine scalar polynomial coordinates; their evaluations equal the corresponding basis coordinates of the original Lie evaluation. Polynomial extensionality on the infinite integer box forces every polynomial coefficient to vanish, giving actual tensor equality.',
    'A finite set of integer evaluations determines all graded array coefficients simultaneously. Genuine finite dimension implies the Artinian minimality of finite intersections of evaluation kernels; minimality makes the selected intersection lie in every evaluation kernel. Complete integer separation then forces it to be zero.',
    'Evaluation on the selected finite integer set is a concrete linear embedding into a finite product of the original Lie algebra. Each component preserves the original Lie bracket exactly. The finite set is selected before the coefficient arrays to be compared; no supplied point-separation or finite-selection hypothesis is used.',
    'The finite integer embedding is specialized to the original native GroupLieAlgebra, using its proved original group nilpotency cutoff and the original tangent model finite dimension. This supplies the coefficient-recovery step required for the paper array lattice discreteness argument; construction of the native array group and the lattice topology remain separate obligations.'
]
remaining = baseline['last_round']['remaining'].replace(
    'Coefficient recovery by sufficiently many integer evaluations, the same-step nilpotency bound for this Lie algebra, construction and identification of its native simply connected array group, array-group topology, discrete cocompact lattice and smooth quotient evaluation remain unproved.',
    'The same-step lower-central cutoff of the genuine array Lie algebra, injectivity of all integer evaluations and simultaneous coefficient recovery by one fixed finite integer evaluation set are now proved, including for the original native model. Construction and identification of its native simply connected array group, array-group topology, discrete cocompact lattice and smooth quotient evaluation remain unproved.')
assert remaining != baseline['last_round']['remaining']
reviews = [
    'PROGRESS. The preceding graded-Lie-array round was authoritatively rechecked and its 1344-source manifest was copied before new proof edits. Retained proof sources and exact selected axiom sets remain fixed.',
    'The ambient scalar-extension lower-central bound is proved by genuine tensor and span inductions. The coefficient layer uses the actual original Lie lower central series and arbitrary scalar polynomials. A pure bracket multiplies those polynomials and lies in the original next layer. No bracket-closure or nilpotence premise about the array algebra is supplied.',
    'The array Lie subalgebra cutoff uses the actual injective inclusion and the genuine Lie ideal map lower-central bound. The native specialization uses the retained native group-to-Lie theorem at the original group nilpotency class. No claim about a group containing input-shift automorphisms or equality of group and Lie lower-central layers is inferred.',
    'Basis-coordinate extraction uses the actual tensor-product basis equivalence. Evaluation is proved compatible on pure tensors and extended by tensor induction. Integer casts form an infinite set in characteristic-zero fields. Polynomial extensionality on that infinite box yields coefficient vanishing; choice assembles an integer input vector from each point of the box. There is no unproved interpolation or separation assumption.',
    'The proof works also for an empty input-variable type and for a zero original Lie algebra. Whole integer evaluation separation does not require finite dimension or a finite variable type. These finiteness hypotheses are used only for choosing a finite evaluation set from the genuine finite-dimensional array coefficient algebra.',
    'Finite selection is proved using Artinian minimality of the actual range of finite kernel intersections. Adding one evaluation makes an intersection smaller; minimality forces reverse inclusion. The selected intersection therefore lies in every evaluation kernel, and the previously proved full separation makes it zero. The selected finite set is fixed before choosing any two coefficient arrays.',
    'The finite evaluation map is a literal linear map into a finite product of original Lie-algebra values, and exact bracket preservation is stated component by component. This does not pretend that a native manifold or a Lie group has already been constructed on that image. The group construction, topology, lattice discreteness and cocompactness still require proofs.',
    'Six new modules contain 15 theorems and two definitions, all 17 declarations selected for kernel audit. No proof holes, new axioms, structures, global instances, unsafe code or resource settings are introduced. Strict focused checks, full build, kernel checks, retained-source and exact-axiom comparisons and final recheck must terminate successfully.',
    remaining
]
source = Path(previous + '-audit.py').read_text(encoding='utf-8')
replacements = {
    "len(baseline['files']) == 1339": "len(baseline['files']) == 1344",
    "'baseline_hash_count': 1339": "'baseline_hash_count': 1344",
    'len(set(names)) == 21': 'len(set(names)) == 17',
    "for values in ds.values() for kind, _ in values) == 14": "for values in ds.values() for kind, _ in values) == 15",
    "for values in ds.values() for kind, _ in values) == 7": "for values in ds.values() for kind, _ in values) == 2",
    "'theorem_count': 14, 'selected_report_count': 21": "'theorem_count': 15, 'selected_report_count': 17",
    "names == registration['names'] and len(names) == 21": "names == registration['names'] and len(names) == 17",
    'len(own) == 1326': 'len(own) == 1332',
    'len(actual) == 6026': 'len(actual) == 6043',
    "len({f['path'] for f in files}) == 1344": "len({f['path'] for f in files}) == 1350",
    'new_theorems=14, new_definitions=7, new_structures=0, new_instances=0, new_axiom_reports=21':
        'new_theorems=15, new_definitions=2, new_structures=0, new_instances=0, new_axiom_reports=17',
    'hindman_module_count=1326': 'hindman_module_count=1332',
    'selected_axiom_report_count=6026, source_scan_module_count=1335':
        'selected_axiom_report_count=6043, source_scan_module_count=1341',
    'new_module_count=5, new_theorem_count=14': 'new_module_count=6, new_theorem_count=15',
    'new_selected_report_count=21': 'new_selected_report_count=17',
    "reference_scope='08_alignment actual native graded polynomial-array coefficient Lie algebra and finite dimension'":
        "reference_scope='08_alignment same-step array Lie nilpotence and coefficient recovery by finitely many integer evaluations'"
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
scope = '''    layers = read('Hindman168/AlignmentLieTensorLayers.lean')
    assert 'LieModule.lowerCentralSeries R L L k' in layers
    assert 'alignmentLieTensorLayer_bracket_next' in layers
    assert 'TensorProduct.induction_on' in layers
    cutoff = read('Hindman168/AlignmentLieArrayNilpotence.lean')
    assert 'LieIdeal.bot_of_map_eq_bot hf' in cutoff
    assert 'nativeLieLowerCentral_nilpotencyClass_bot' in cutoff
    separation = read('Hindman168/AlignmentLieArrayIntegerSeparation.lean')
    assert 'TensorProduct.equivFinsuppOfBasisRight' in separation
    assert 'MvPolynomial.funext_set' in separation
    assert 'Set.infinite_range_of_injective Int.cast_injective' in separation
    selection = read('Hindman168/AlignmentFiniteEvaluationSelection.lean')
    assert 'IsArtinian.set_has_minimal' in selection
    assert '⨅ i ∈ S, (f i).ker' in selection
    assert 'alignmentLiePolynomialArrays_finiteDimensional' in selection
    embedding = read('Hindman168/AlignmentLieArrayFiniteEmbedding.lean')
    assert 'alignmentLieArrayFiniteEvaluation_exists_injective' in embedding
    assert 'alignmentLieArrayFiniteEvaluation_bracket' in embedding
    native = read('Hindman168/AlignmentNativeLieArrayFiniteEvaluations.lean')
    assert 'GroupLieAlgebra I G' in native
    assert 'nativeLieLowerCentral_nilpotencyClass_bot' in native
'''
assert source.count(anchor) == 1
source = source.replace(anchor, scope + anchor, 1)
ast.parse(source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
focused = Path('check-alignment-graded-lie-arrays.py').read_text(encoding='utf-8')
assert focused.count("prefix = 'round-alignment-graded-lie-arrays'") == 1
focused = focused.replace("prefix = 'round-alignment-graded-lie-arrays'", 'prefix = ' + repr(prefix))
Path('check-alignment-array-separation.py').write_text(focused, encoding='utf-8')
print(json.dumps({'prepared_modules': len(modules), 'theorems': 15, 'definitions': 2, 'declarations': 17}))
