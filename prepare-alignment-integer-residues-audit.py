from pathlib import Path
import ast
import json
import re

prefix = 'round-alignment-integer-residues'
previous = 'round-alignment-palette-slots'
modules = ['Hindman168/' + name + '.lean' for name in [
    'AlignmentIntegerPairScales', 'AlignmentIntegerResidues', 'AlignmentIntegerNumerators',
    'AlignmentMasterResidueData', 'AlignmentIntegerSlotShifts', 'AlignmentIntegerArrayArguments']]
ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|def)\s+(\w+)',
    Path(p).read_text(encoding='utf-8'), re.M) for p in modules}
tms = sum(k == 'theorem' for v in ds.values() for k, _ in v)
defs = sum(k == 'def' for v in ds.values() for k, _ in v)
assert (tms, defs, sum(map(len, ds.values()))) == (25, 9, 34)
baseline = json.loads(Path(prefix + '-baseline.json').read_text(encoding='utf-8'))
assert len(baseline['files']) == 1323
assert baseline == json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
components = [
    'Actual Fin n adding pairs map to the natural-index adding relation used by the original master scales. The original source scale is divisible by the target scale times primorial(w)^w; no replacement scale family is used. Products of raw unit coordinates remain coprime to the actual small-prime modulus.',
    'A bounded residue rho is constructed modulo the full modulus M*V using coprimality. Its progression shift is the actual integer quotient (q-t*rho)/M. The quotient is exact and divisible by V, and rho is divisible by W whenever W divides q and M*V. The own-letter integer identity holds for every signed exponent and pivot value without requiring t to divide q.',
    'For the actual master pair scales and every common positive denominator q0, q0*primorial(w) divides primorial(w)^w once w is at least q0+1. The natural integer numerator is defined by exact natural division. Its rational cast equals precisely h_A/(q0*h_U)*t_A and it is divisible by primorial(w).',
    'Smoothness of the actual master modulus makes every target tail product a unit modulo M*primorial(w)^w. All actual pairs admit the required bounded residue data at one threshold independent of raw unit values. Residues are less than M^2, progression shifts are divisible by primorial(w)^w, and each fixed positive integer eventually divides them uniformly over all raw unit values and all pivots and pairs.',
    'The actual finite pair coordinates define the numerical slot shift s(v)=sum(v_e*rho_e). Zero, addition and unit-coordinate translation are exact; small-prime divisibility is preserved. A uniform bound controls its absolute value by L times the fixed slot absolute-coordinate weight.',
    'The numerical array argument is the actual tail product times p+s(v), plus M times the own-target progression-coordinate sum. Advancing both slot and array coordinates by a signed own-target unit changes this numerical argument by m*q_e. This proves the numerical own-letter interpretation only; an arbitrary cumulative jump is not asserted to translate the original pivot orbit.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional Prediction includes actual admissible parameters, positive finite scale-list closure, common native unit observables and complete fixed-ultrafilter calibration and count limits. '
    'Conditional Alignment includes the canonical finite-word schedule, actual execution, positive palette-scale budgets, common positive denominator and certified actual auxiliary visits. '
    'Integer realization now proves the actual master pair scale relation, exact natural numerator with its original rational value, bounded full-modulus residues, all required divisibilities, the uniform eventual fixed-integer divisibility, finite numerical slot bounds and the numerical own-target array-letter identity. '
    'HasAlignmentMonomialRecurrence remains an explicit unproved input. Its genuine nilpotent recurrence proof, the actual native polynomial-array model action with its required nilpotence and translation compatibility, microcell boundary and point-law estimates, and positive-probability Alignment bounds remain unproved. '
    'Final ordered positive rapidly separated monochromatic extraction is incomplete. No unavoidable blocker is established. '
    'A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The preceding palette-slots round was rechecked successfully and its authoritative 1323-source manifest was copied before proof edits. All retained proof sources and exact selected axiom sets remain fixed.',
    'The finite pairs are mapped into the original natural-index Chain.AddsTo relation using all four actual order conditions and nonempty tails. The natural block image lies inside range n. Consequently the original reversed-weight master-scale divisibility applies to the actual source and target blocks.',
    'Coprimality supplies a bounded residue modulo M*V, not merely modulo M. The full modulus is necessary for V-divisibility of the exact progression quotient. Small-prime residue divisibility follows by Euclid cancellation of the coprime target tail. No divisibility of q by that tail is introduced.',
    'Natural subtraction is not used for a potentially negative progression shift. The quotient is an integer expression (q-t*rho)/M and its exactness follows from the full congruence. All numerical identities quantify over arbitrary signed integer exponents.',
    'The denominator absorption threshold q0+1 is independent of raw variables, pivot, pair, and model complexity. The numerator uses exact natural division, with a proved factorization and a proved rational value equal to the paper formula. A floor or an arbitrary integer with merely compatible divisibility is not substituted for that formula.',
    'Smoothness and the actual primorial power divisor come from MasterParameterConditions. These master conditions already have a genuine construction in the retained sources; the residue theorem does not assume the desired congruence or Alignment success. Raw unit conditions imply tail coprimality modulo the full smooth modulus.',
    'The eventual fixed-integer divisibility statement fixes its threshold before universally quantifying over all raw unit values, pivots and actual adding pairs. This verifies the uniformity needed when the earlier raw variables are conditioned on in the paper.',
    'The finite numerical slot sum uses exactly the actual finite adding-pair coordinates. Its signed unit update, small-prime divisibility and absolute-coordinate weight bound are proved. The residue bound rho<M^2 uses the actual primorial-power divisor of M.',
    'The numerical array progression sums precisely the coordinates whose target tail is T. Updating an own-target letter moves both the slot and its progression coordinate. The resulting shift m*q_e is derived from the exact integer equation. This numerical calculation does not assert a group action, its nilpotence or compatibility with native observables.',
    'Six new modules contain 25 theorems and 9 definitions; all 34 declarations are selected for kernel audit. No proof holes, new axioms, structures, global instances, unsafe code or resource increases are introduced. Strict focused checks, full build, kernel checking, retained-source and axiom comparisons and a final recheck must terminate successfully.',
    remaining
]
source = Path(previous + '-audit.py').read_text(encoding='utf-8')
replacements = {
    "len(baseline['files']) == 1317": "len(baseline['files']) == 1323",
    "'baseline_hash_count': 1317": "'baseline_hash_count': 1323",
    'len(set(names)) == 45': 'len(set(names)) == 34',
    "for values in ds.values() for kind, _ in values) == 33": "for values in ds.values() for kind, _ in values) == 25",
    "for values in ds.values() for kind, _ in values) == 12": "for values in ds.values() for kind, _ in values) == 9",
    "'theorem_count': 33, 'selected_report_count': 45": "'theorem_count': 25, 'selected_report_count': 34",
    "names == registration['names'] and len(names) == 45": "names == registration['names'] and len(names) == 34",
    'len(own) == 1305': 'len(own) == 1311',
    'len(actual) == 5910': 'len(actual) == 5944',
    "len({f['path'] for f in files}) == 1323": "len({f['path'] for f in files}) == 1329",
    'new_theorems=33, new_definitions=12, new_structures=0, new_instances=0, new_axiom_reports=45':
        'new_theorems=25, new_definitions=9, new_structures=0, new_instances=0, new_axiom_reports=34',
    'hindman_module_count=1305': 'hindman_module_count=1311',
    'selected_axiom_report_count=5910, source_scan_module_count=1314':
        'selected_axiom_report_count=5944, source_scan_module_count=1320',
    'new_module_count=6, new_theorem_count=33': 'new_module_count=6, new_theorem_count=25',
    'new_selected_report_count=45': 'new_selected_report_count=34',
    "reference_scope='08_alignment complete canonical finite-word planning with positive global Prediction scale closure and actual auxiliary jump and terminal visit tables'":
        "reference_scope='08_alignment integer residue shifts, full smooth-modulus divisibilities and numerical own-target array arguments'"
}
for old in replacements:
    assert old in source, old
pattern = re.compile('|'.join(re.escape(s) for s in sorted(replacements, key=len, reverse=True)))
source = pattern.sub(lambda m: replacements[m.group()], source)
values = {'PREFIX': prefix, 'OLD': previous, 'MODULES': modules,
    'COMPONENTS': components, 'REMAINING': remaining,
    'EXPECTED_NEW_AXIOM_FREE': {'Hindman168.alignmentProgressionShift'}}
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
scope = '''    residue = read('Hindman168/AlignmentMasterResidueData.lean')
    statement = residue.split('theorem alignmentMaster_eventual_residue_divisibility', 1)[1].split(' := by', 1)[0]
    assert statement.index('∀ᶠ w in atTop') < statement.index('∀ t : Fin n') < statement.index('∀ i : Fin n')
    assert 'MasterParameterConditions n A D F' in statement
    assert 'HasAlignmentMonomialRecurrence' not in residue
    exact = read('Hindman168/AlignmentIntegerResidues.lean')
    assert '((q : ℤ) - (t : ℤ) * ρ) / M' in exact
    assert 'Nat.exists_mul_mod_eq_of_coprime' in exact
    assert 'alignment_residue_progression_exact' in exact
    array = read('Hindman168/AlignmentIntegerArrayArguments.lean')
    assert 'if e.targetTail = T then u e * Δ e else 0' in array
    assert 'alignmentIntegerArrayArgument_own_letter' in array
'''
assert source.count(anchor) == 1
source = source.replace(anchor, scope + anchor, 1)
ast.parse(source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
focused = Path('check-alignment-palette-slots.py').read_text(encoding='utf-8')
assert focused.count("prefix = 'round-alignment-palette-slots'") == 1
focused = focused.replace("prefix = 'round-alignment-palette-slots'", 'prefix = ' + repr(prefix))
Path('check-alignment-integer-residues.py').write_text(focused, encoding='utf-8')
print(json.dumps({'prepared_modules': len(modules), 'theorems': tms, 'definitions': defs,
    'declarations': tms + defs}))
