from pathlib import Path
import ast
import json
import re

prefix = 'round-alignment-residue-exposure'
previous = 'round-alignment-integer-residues'
modules = ['Hindman168/' + n + '.lean' for n in [
    'AlignmentResidueRepresentative', 'AlignmentRawExposure',
    'AlignmentExposedResidues', 'AlignmentExposedArrayOffsets']]
ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|def)\s+(\w+)',
    Path(p).read_text(encoding='utf-8'), re.M) for p in modules}
assert sum(k == 'theorem' for v in ds.values() for k, _ in v) == 18
assert sum(k == 'def' for v in ds.values() for k, _ in v) == 5
assert sum(map(len, ds.values())) == 23
baseline = json.loads(Path(prefix + '-baseline.json').read_text(encoding='utf-8'))
assert baseline == json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert len(baseline['files']) == 1329
components = [
    'The bounded full-modulus residue solution is unique. A canonical representative depends on the numerator, tail product and modulus alone, and is invariant when numerator and tail product change within their respective residue classes.',
    'The raw exposure predicate fixes only earlier coordinates outside the target tail and only full-modulus residues inside that tail. It leaves all coordinates at and after the pivot unrestricted. Source blocks are disjoint from their own target tails. All earlier block products and all pair numerators have fixed full-modulus residues; own-target numerators are fixed as complete integers.',
    'Actual pair residue data are now canonical functions of the actual master numerator and target tail product. Their positivity bounds, small-prime divisibility, full congruence, progression divisibility and integer identity are retained. The actual exposure fixes every pair residue and every finite numerical slot shift, including residues for other targets.',
    'The exposure fixes target array residues at the original smooth modulus. The exact canonical progression increment is affine in the changing own-target tail product: its M-multiple changes by minus the tail-product change times the fixed residue. Summing all own-target coordinates gives the exact corresponding affine change in the entire numerical array progression.'
]
remaining = baseline['last_round']['remaining'].replace(
    'Integer realization now proves the actual master pair scale relation, exact natural numerator with its original rational value, bounded full-modulus residues, all required divisibilities, the uniform eventual fixed-integer divisibility, finite numerical slot bounds and the numerical own-target array-letter identity.',
    'Integer realization now proves the actual master pair scale relation, exact natural numerator with its original rational value, canonical bounded full-modulus residues, all required divisibilities, uniform eventual fixed-integer divisibility, finite numerical slot bounds and the numerical own-target array-letter identity. The actual earlier-variable exposure fixes every residue and slot shift, full own-target numerators and array residues; exact affine tail dependence of each progression and the whole own-target progression sum is proved.')
assert remaining != baseline['last_round']['remaining']
reviews = [
    'PROGRESS. The preceding integer-residues round was rechecked successfully and its authoritative 1329-source manifest was copied before new proof edits. Retained proof sources and exact selected axiom sets remain fixed.',
    'Coprime cancellation and the strict bounds below the full modulus prove uniqueness of the residue. The canonical representative is chosen from numerical q,t,L alone. Its congruence invariance therefore fixes an actual function rather than merely permitting a convenient fresh representative in each exposure.',
    'The exposure matches the paper: exact values outside the selected tail are fixed only for earlier coordinates, and residues modulo L are fixed inside the selected tail. It does not fix the pivot or later coordinates and does not incorrectly fix the exact values inside the target tail.',
    'All pair sources and target tails lie before the pivot, so their products have fixed residues. Exact natural numerator coefficients depend only on the fixed denominator, w and pair. Each source block is disjoint from its own target tail, so each own-target full integer numerator is fixed. Numerators for other targets are only claimed fixed modulo L.',
    'Canonical residues retain the actual master bounds, divisibilities, full congruence and signed integer identity by uniqueness of the previously constructed bounded solution. Full smooth-modulus coprimality comes from the genuine retained master arithmetic, not an assumed congruence solution. All pair residues and the entire finite slot sum are invariant under exposure.',
    'The target array residue uses integer remainder because the slot shift is signed. Reduction from L to M follows from M dividing L. Fixed tail residues consequently fix r-star and every r-v for fixed pivot residue and slot shift. The unknown microcell origin is not fixed by this arithmetic theorem.',
    'The exact progression difference is affine in the changing target tail product; full own-target numerator and canonical residue invariance are used. Summation includes precisely the coordinates whose target tail is the exposed T. Other-target progression terms are not asserted to have this affine formula.',
    'Four modules contain 18 theorems and 5 definitions; all 23 declarations are selected for kernel audit. No proof holes, new axioms, structures, global instances, unsafe code or resource changes are introduced. Strict focused checks, full build, kernel checking, exact retained-source and axiom comparisons and final recheck must terminate successfully.',
    'These are arithmetic exposure and numerical array-coefficient results. They do not prove the conditional sampling domination, boundary error, ordinary polynomial logarithm of a native model array, nilpotent model action, face invariance or positive-probability Alignment.',
    remaining
]
source = Path(previous + '-audit.py').read_text(encoding='utf-8')
replacements = {
    "len(baseline['files']) == 1323": "len(baseline['files']) == 1329",
    "'baseline_hash_count': 1323": "'baseline_hash_count': 1329",
    'len(set(names)) == 34': 'len(set(names)) == 23',
    "for values in ds.values() for kind, _ in values) == 25": "for values in ds.values() for kind, _ in values) == 18",
    "for values in ds.values() for kind, _ in values) == 9": "for values in ds.values() for kind, _ in values) == 5",
    "'theorem_count': 25, 'selected_report_count': 34": "'theorem_count': 18, 'selected_report_count': 23",
    "names == registration['names'] and len(names) == 34": "names == registration['names'] and len(names) == 23",
    'len(own) == 1311': 'len(own) == 1315',
    'len(actual) == 5944': 'len(actual) == 5967',
    "len({f['path'] for f in files}) == 1329": "len({f['path'] for f in files}) == 1333",
    'new_theorems=25, new_definitions=9, new_structures=0, new_instances=0, new_axiom_reports=34':
        'new_theorems=18, new_definitions=5, new_structures=0, new_instances=0, new_axiom_reports=23',
    'hindman_module_count=1311': 'hindman_module_count=1315',
    'selected_axiom_report_count=5944, source_scan_module_count=1320':
        'selected_axiom_report_count=5967, source_scan_module_count=1324',
    'new_module_count=6, new_theorem_count=25': 'new_module_count=4, new_theorem_count=18',
    'new_selected_report_count=34': 'new_selected_report_count=23',
    "reference_scope='08_alignment integer residue shifts, full smooth-modulus divisibilities and numerical own-target array arguments'":
        "reference_scope='08_alignment conditional face invariance: exposed residue data and exact affine progression dependence'"
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
scope = '''    exposure = read('Hindman168/AlignmentRawExposure.lean')
    predicate = exposure.split('def alignmentRawExposure', 1)[1].split('theorem', 1)[0]
    assert "(∀ j, j < i → j ∉ T → t j = t' j)" in predicate
    assert "(∀ j ∈ T, Nat.ModEq L (t j) (t' j))" in predicate
    assert 'alignmentPair_source_disjoint_tail' in exposure
    representative = read('Hindman168/AlignmentResidueRepresentative.lean')
    assert 'alignment_bounded_residue_unique' in representative
    assert 'alignmentResidueRepresentative_congr' in representative
    fixed = read('Hindman168/AlignmentExposedResidues.lean')
    assert 'alignmentRawExposure_slot_shift_eq' in fixed
    offsets = read('Hindman168/AlignmentExposedArrayOffsets.lean')
    assert 'alignmentRawExposure_arrayProgression_difference' in offsets
    assert 'alignmentRawExposure_arrayResidue_eq' in offsets
'''
assert source.count(anchor) == 1
source = source.replace(anchor, scope + anchor, 1)
ast.parse(source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
focused = Path('check-alignment-integer-residues.py').read_text(encoding='utf-8')
assert focused.count("prefix = 'round-alignment-integer-residues'") == 1
focused = focused.replace("prefix = 'round-alignment-integer-residues'", 'prefix = ' + repr(prefix))
Path('check-alignment-residue-exposure.py').write_text(focused, encoding='utf-8')
print(json.dumps({'prepared_modules': len(modules), 'theorems': 18, 'definitions': 5, 'declarations': 23}))
