from pathlib import Path
import ast
import json
import re

prefix = 'round-alignment-graded-lie-arrays'
previous = 'round-alignment-polynomial-arrays'
modules = ['Hindman168/' + n + '.lean' for n in [
    'AlignmentLieLowerCentralBrackets', 'AlignmentGradedLiePolynomialArrays',
    'AlignmentLieArrayFiniteDimension', 'AlignmentLieArrayEvaluation',
    'AlignmentNativeLieArrayCoefficients']]
ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|def)\s+(\w+)',
    Path(p).read_text(encoding='utf-8'), re.M) for p in modules}
assert sum(k == 'theorem' for v in ds.values() for k, _ in v) == 14
assert sum(k == 'def' for v in ds.values() for k, _ in v) == 7
assert sum(map(len, ds.values())) == 21
baseline = json.loads(Path(prefix + '-baseline.json').read_text(encoding='utf-8'))
assert baseline == json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert len(baseline['files']) == 1339
components = [
    'The genuine lower central series of an arbitrary original Lie algebra satisfies [LC_j,LC_k] <= LC_(j+k+1), using Jacobi and actual linear-span induction. The weighted estimate covers all degrees including zero and gives the paper positive-degree coefficient condition without a supplied bracket-compatibility hypothesis.',
    'The actual coefficient tensor MvPolynomial sigma R tensor_R L carries the scalar-extension Lie bracket. Monomials of degree d have coefficients in original Lie lower-central level d-1; degree zero has unrestricted coefficients. Their linear span is proved bracket closed and defines the actual graded polynomial-array Lie subalgebra.',
    'Original Lie lower-central vanishing at s forces every allowed monomial above degree s to vanish. The whole array coefficient space lies in the range of the genuine bounded-total-degree polynomial tensor inclusion. For finite input-variable types and finite-dimensional original Lie algebras, the actual array Lie algebra is proved finite dimensional.',
    'Literal coefficient-array evaluation is an actual Lie homomorphism to the original Lie algebra, with polynomial and monomial evaluation formulas. Its restriction to the graded array Lie algebra maps each original array lower-central level into the corresponding original Lie-algebra lower-central level.',
    'The coefficient Lie algebra is specialized to the original native GroupLieAlgebra of the given Lie group. Its finite dimension and high-degree cutoff follow from the retained proved original group-to-Lie nilpotency theorem at Group.nilpotencyClass, without a replacement Lie algebra or an assumed native Lie filtration cutoff.'
]
remaining = baseline['last_round']['remaining'].replace(
    'Identification with the paper finite-dimensional native Lie array group, coefficient bounds and topology, discrete cocompact lattice and smooth evaluation remain unproved.',
    'The genuine original native Lie polynomial-array coefficient algebra, bracket closure, high-degree cutoff and finite dimension are now proved; literal Lie evaluation homomorphisms and their lower-central compatibility are constructed. Coefficient recovery by sufficiently many integer evaluations, the same-step nilpotency bound for this Lie algebra, construction and identification of its native simply connected array group, array-group topology, discrete cocompact lattice and smooth quotient evaluation remain unproved.')
assert remaining != baseline['last_round']['remaining']
reviews = [
    'PROGRESS. The preceding polynomial-array round was authoritatively rechecked and its 1339-source manifest was copied before new proof edits. Retained proof sources and exact selected axiom sets remain fixed.',
    'The bracket-layer estimate is proved for the actual Mathlib lower central series. Induction on the first level expands its successor as a linear span of genuine brackets. Jacobi moves a fixed second coefficient through the generator, and linearity covers zero, sums and scalar multiples. It is not a theorem whose hypotheses already assume the desired filtration estimate.',
    'Mathlib starts the lower central series at the whole Lie algebra as level zero. The paper degree d>0 condition is therefore level d-1. Truncated natural subtraction makes degree zero unrestricted. The proven inequality d+e-1 <= (d-1)+(e-1)+1 handles zero degrees correctly; bracket membership uses antitonicity, never the reversed filtration inclusion.',
    'The ambient object uses scalar extension of an arbitrary Lie algebra by genuine multivariable polynomials. It requires no associative multiplication on the original Lie algebra. The pure-tensor bracket multiplies the actual monomials and brackets the actual original coefficients; bilinear span induction proves closure of the complete coefficient space.',
    'Finite dimension is derived from genuine original lower-central vanishing, not provided as a new hypothesis on the array algebra. An allowed degree greater than s has its original coefficient equal to zero. All other generators belong to the tensor image of the actual bounded-total-degree polynomial submodule. That domain is finite dimensional for finite input-variable types and a finite-dimensional original Lie algebra.',
    'Evaluation uses the genuine polynomial algebra evaluation and tensor lift of scalar multiplication. Its Lie homomorphism law is proved on pure tensors and extended by two tensor inductions. The restricted map respects the original lower central series. This compatibility alone is not asserted to prove injectivity, coefficient recovery, or the array algebra nilpotency cutoff.',
    'The native specialization uses GroupLieAlgebra I G itself and the retained proved group-to-Lie cutoff at the original group nilpotency class. The tangent model finite-dimensional instance is installed locally from the original model E. No global instance, smoothness assumption stronger than the original setting, surrogate model or equality of group and Lie lower-central layers is introduced.',
    'Five new modules contain 14 theorems and seven definitions, all 21 declarations selected for kernel audit. No holes, new axioms, structures, global instances, unsafe code or resource settings are introduced. Strict focused checks, full build, kernel checks, retained-source and exact-axiom comparisons and final recheck must terminate successfully.',
    remaining
]
source = Path(previous + '-audit.py').read_text(encoding='utf-8')
replacements = {
    "len(baseline['files']) == 1333": "len(baseline['files']) == 1339",
    "'baseline_hash_count': 1333": "'baseline_hash_count': 1339",
    'len(set(names)) == 38': 'len(set(names)) == 21',
    "for values in ds.values() for kind, _ in values) == 25": "for values in ds.values() for kind, _ in values) == 14",
    "for values in ds.values() for kind, _ in values) == 13": "for values in ds.values() for kind, _ in values) == 7",
    "'theorem_count': 25, 'selected_report_count': 38": "'theorem_count': 14, 'selected_report_count': 21",
    "names == registration['names'] and len(names) == 38": "names == registration['names'] and len(names) == 21",
    'len(own) == 1321': 'len(own) == 1326',
    'len(actual) == 6005': 'len(actual) == 6026',
    "len({f['path'] for f in files}) == 1339": "len({f['path'] for f in files}) == 1344",
    'new_theorems=25, new_definitions=13, new_structures=0, new_instances=0, new_axiom_reports=38':
        'new_theorems=14, new_definitions=7, new_structures=0, new_instances=0, new_axiom_reports=21',
    'hindman_module_count=1321': 'hindman_module_count=1326',
    'selected_axiom_report_count=6005, source_scan_module_count=1330':
        'selected_axiom_report_count=6026, source_scan_module_count=1335',
    'new_module_count=6, new_theorem_count=25': 'new_module_count=5, new_theorem_count=14',
    'new_selected_report_count=38': 'new_selected_report_count=21',
    "reference_scope='08_alignment integer polynomial array groups, input shifts, lattice coset evaluation and model linear orbits'":
        "reference_scope='08_alignment actual native graded polynomial-array coefficient Lie algebra and finite dimension'"
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
scope = '''    brackets = read('Hindman168/AlignmentLieLowerCentralBrackets.lean')
    assert 'LieModule.lowerCentralSeries R L L (j + k + 1)' in brackets
    assert 'Submodule.span_induction' in brackets and 'rw [lie_lie]' in brackets
    assert 'LieModule.antitone_lowerCentralSeries' in brackets
    coefficients = read('Hindman168/AlignmentGradedLiePolynomialArrays.lean')
    assert 'd.sum (fun _ n => n) - 1' in coefficients
    assert 'LieAlgebra.ExtendScalars.bracket_tmul' in coefficients
    assert 'Submodule.span_induction₂' in coefficients
    finite = read('Hindman168/AlignmentLieArrayFiniteDimension.lean')
    assert '(MvPolynomial.restrictTotalDegree σ R s).subtype.rTensor L' in finite
    assert 'alignmentLieArrayGenerator_highDegree_zero' in finite
    assert 'Submodule.finiteDimensional_of_le' in finite
    evaluation = read('Hindman168/AlignmentLieArrayEvaluation.lean')
    assert 'TensorProduct.lift' in evaluation and 'MvPolynomial.aeval u' in evaluation
    assert 'LieIdeal.map_lowerCentralSeries_le' in evaluation
    native = read('Hindman168/AlignmentNativeLieArrayCoefficients.lean')
    assert 'GroupLieAlgebra I G' in native
    assert 'nativeLieLowerCentral_nilpotencyClass_bot' in native
    assert 'inferInstanceAs (FiniteDimensional ℝ E)' in native
'''
assert source.count(anchor) == 1
source = source.replace(anchor, scope + anchor, 1)
ast.parse(source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
focused = Path('check-alignment-polynomial-arrays.py').read_text(encoding='utf-8')
assert focused.count("prefix = 'round-alignment-polynomial-arrays'") == 1
focused = focused.replace("prefix = 'round-alignment-polynomial-arrays'", 'prefix = ' + repr(prefix))
Path('check-alignment-graded-lie-arrays.py').write_text(focused, encoding='utf-8')
print(json.dumps({'prepared_modules': len(modules), 'theorems': 14, 'definitions': 7, 'declarations': 21}))
