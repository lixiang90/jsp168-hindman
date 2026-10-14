from pathlib import Path
import ast
import json
import re

modules = ['Hindman168/' + n + '.lean' for n in [
    'AlignmentPlanPositivity', 'AlignmentGlobalPaletteScales', 'AlignmentAuxiliaryWords',
    'AlignmentAuxiliaryPlanSlots', 'AlignmentAuxiliaryTerminalSlots', 'AlignmentFiniteWordBudgets']]
components = [
    'Leading-factor positivity is proved through the actual fixed-pivot predecessor recursion and through all future-augmented pivot requests. Canonical terminal leading factors equal one. All stage target leading factors are therefore genuinely positive; none is assumed positive merely because it appears in a finite table.',
    'One global finite rational palette-index list includes every stage recurrence index and every original request index at all intermediate and final scales. Closing this list under all final block products yields the positive Prediction scale list. Its positivity, exact stage-query membership and full final block-product closure are proved from the actual canonical schedule and positive choices.',
    'Unit translation by each original generator implies the exact translation by every signed integer power. Actual ordered word actions induce their explicitly computed integer-vector displacements. Auxiliary visit tables include zero, complete endpoints and all unit-power intermediate positions for both signs, following the right-to-left evaluation of a left action.',
    'The finite auxiliary frontier executes the backward-stored plan in its genuine forward order. Reachability alone places all pivot scales in the actual frontier. The same actual reachability trace has its endpoint in the prescribed auxiliary frontier, and a strengthened safe trace certifies every intermediate jump visit belongs to the full finite plan table.',
    'The prescribed per-pivot auxiliary table additionally includes every original terminal-test visit from every possible endpoint. The same successful pivot centers and same final scale in the actual schedule trace satisfy the strengthened safe trace and all terminal visit bounds, whenever generators translate the auxiliary coordinates by one and the initial coordinates are zero.',
    'The canonical finite-word theorem now chooses the schedule, positive Prediction scale list, common positive denominator and all finite auxiliary tables before any model data. It executes all canonical pivots and targets, gives full original final-scale comparisons through the retained actual trace, and certifies the auxiliary safety of that same execution for every compatible coordinate map. Nilpotent monomial recurrence existence is still an explicit unproved input; no actual integer-model action or positive-probability Alignment result is claimed.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional Prediction includes actual admissible parameters, finite positive scale-list closure, all scale/color indices, globally unit-range common native observables and actual fixed-ultrafilter calibration and complete count limits. '
    'Conditional Alignment now includes the full canonical finite-word construction: backward planning, actual forward execution, one common positive integer denominator, complete positive global scale and palette-index catalogues, final block-product closure, finite auxiliary tables containing zero, and certified actual jump and terminal-test visits at the same successful centers. '
    'HasAlignmentMonomialRecurrence remains an explicit unproved input. Its genuine nilpotent recurrence existence proof, the actual integer residue/polynomial array action with the required nilpotence and translation compatibility, and positive-probability Alignment bounds remain unproved. '
    'Final ordered positive rapidly separated monochromatic extraction is also incomplete. No unavoidable blocker is established. '
    'A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The preceding schedule-execution round was rechecked successfully. Its authoritative 1317-source manifest was copied before new proof edits. All retained proof sources and exact selected axiom sets remain fixed.',
    'The previously missing positivity of stage target leading budgets is derived by induction on the actual backward plan fit. The recursive requests are mapped all-choice predecessors of the shorter prefix, not the unchanged original prefix. The all-pivot fit then supplies all actual later multiplier positivity before future leading factors are used. Canonical original factors equal one.',
    'The global palette budget includes actual recurrence stage targets and original terminal requests. Multiplication by every intermediate or final block product supplies all queried palette indices, and closure adds every final subset product. Positivity follows from the proved stage budgets and scale catalogues. A finite set declaration is not used as a substitute for these proofs.',
    'A generic signed-power translation lemma is proved from the single-step action law. Its inverse step follows by applying that same law to the inverse-translated state. Only the auxiliary integer vectors are commutative; the actual model group and its ordered words remain arbitrary noncommutative groups.',
    'Word visits process the tail first, as required by a left action. Every power z includes all m between min(0,z) and max(0,z), covering negative powers, zero, and internal unit steps. This avoids the false shortcut of treating a completed word endpoint or its written prefixes alone as the actual visited positions.',
    'The auxiliary frontier follows the reverse storage order of the plan and starts at the prescribed initial slot set. The reachability-to-frontier proof verifies actual scale catalogue membership at every recursive endpoint. A strengthened recursive safe trace records the same admitted choices and literal word actions, while bounding every intermediate visit in the finite global plan table.',
    'Per-pivot tables include zero and all original terminal-word visits from every possible successful endpoint, not just recurrence jumps. The same actual schedule realization is upgraded to a slot-safe realization. It uses the exact original successful center and final comparisons at each pivot. No separate convenient center is chosen to satisfy the slot statement.',
    'The auxiliary compatibility and zero-initial-position conditions are explicit universally quantified conditions on coordinate maps, exactly matching the paper auxiliary-translation assumption. They are not asserted for an unconstructed integer action. The actual residue and polynomial-array action, its nilpotence and its compatibility must still be proved in the integer realization.',
    'The assembled theorem fixes its canonical schedule and positive Prediction scale list before the common positive denominator, and fixes all these before model groups, actions, generators, palettes and initial centers. Its finite slot tables are computed solely from the fixed plan, denominator, scale catalogue and terminal words; they contain no threshold, model complexity or actual state data.',
    'An explicit actual-state visit relation follows the right-to-left evaluation and every signed unit-power step. Each such actual visited state has exactly a displacement in the finite word visit table. The slot membership implication consequently covers actual intermediate states, not only a formal list of vector sums.',
    'Six modules contain 33 theorems and 12 definitions with all 45 declaration names selected for kernel audit. No new structures, instances, proof holes, unsafe code, resource settings or unproved axioms are introduced. Strict focused checks, full build, kernel checking, exact retained source/dependency comparisons and a final recheck must all terminate successfully.',
    remaining
]
source = Path('round-alignment-schedule-execution-audit.py').read_text(encoding='utf-8')
replacements = {
    "len(baseline['files']) == 1313": "len(baseline['files']) == 1317",
    "'baseline_hash_count': 1313": "'baseline_hash_count': 1317",
    'len(set(names)) == 38': 'len(set(names)) == 45',
    "for values in ds.values() for kind, _ in values) == 26": "for values in ds.values() for kind, _ in values) == 33",
    "for values in ds.values() for kind, _ in values) == 12": "for values in ds.values() for kind, _ in values) == 12",
    "'theorem_count': 26, 'selected_report_count': 38": "'theorem_count': 33, 'selected_report_count': 45",
    "names == registration['names'] and len(names) == 38": "names == registration['names'] and len(names) == 45",
    'len(own) == 1299': 'len(own) == 1305',
    'len(actual) == 5865': 'len(actual) == 5910',
    "len({f['path'] for f in files}) == 1317": "len({f['path'] for f in files}) == 1323",
    'new_theorems=26, new_definitions=12, new_structures=0, new_instances=0, new_axiom_reports=38':
        'new_theorems=33, new_definitions=12, new_structures=0, new_instances=0, new_axiom_reports=45',
    'hindman_module_count=1299': 'hindman_module_count=1305',
    'selected_axiom_report_count=5865, source_scan_module_count=1308':
        'selected_axiom_report_count=5910, source_scan_module_count=1314',
    'new_module_count=4, new_theorem_count=26': 'new_module_count=6, new_theorem_count=33',
    'new_selected_report_count=38': 'new_selected_report_count=45',
    "reference_scope='08_alignment common global denominator and actual multi-pivot execution for every canonical target and ordered subset test'":
        "reference_scope='08_alignment complete canonical finite-word planning with positive global Prediction scale closure and actual auxiliary jump and terminal visit tables'"
}
for before in replacements:
    assert before in source, before
pattern = re.compile('|'.join(re.escape(s) for s in sorted(replacements, key=len, reverse=True)))
source = pattern.sub(lambda m: replacements[m.group()], source)
values = {'PREFIX': 'round-alignment-palette-slots', 'OLD': 'round-alignment-schedule-execution',
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
anchor = "    prior = read('Hindman168/PrincipalPredictionModels.lean')\n"
scope = '''    statement = read('Hindman168/AlignmentFiniteWordBudgets.lean').split(
        'theorem alignment_finite_word_budgets', 1)[1].split(' := by', 1)[0]
    assert statement.index('∃ schedule') < statement.index('∃ A') < statement.index('∃ q₀') < statement.index('∀ (G : Fin n')
    assert 'hrec : HasAlignmentMonomialRecurrence s' in statement
    assert 'schedule.map AlignmentPlannedPivot.pivot = List.finRange n' in statement
    assert 'FiniteScaleClosure (alignmentScheduleFinalScales schedule {fun _ => 1}) A' in statement
    assert '(∀ a ∈ A, 0 < a)' in statement
    assert 'alignmentScheduleRealizes G X q₀ L palette (alignmentCanonicalRequests n) centers' in statement
    assert 'alignmentScheduleSlotsRealizes G X q₀' in statement
    assert '∀ position' in statement and '(∀ i, position i (centers i) = 0)' in statement
    visits = read('Hindman168/AlignmentAuxiliaryWords.lean')
    assert 'Finset.Icc (min 0 z) (max 0 z)' in visits
    assert 'alignment_action_integer_translation' in visits
'''
assert source.count(anchor) == 1
source = source.replace(anchor, scope + anchor, 1)
ast.parse(source)
Path('round-alignment-palette-slots-audit.py').write_text(source, encoding='utf-8')
focused = Path('check-alignment-schedule-execution.py').read_text(encoding='utf-8')
assert focused.count("prefix = 'round-alignment-schedule-execution'") == 1
focused = focused.replace("prefix = 'round-alignment-schedule-execution'", "prefix = 'round-alignment-palette-slots'")
Path('check-alignment-palette-slots.py').write_text(focused, encoding='utf-8')
ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+(\w+)',
    Path(p).read_text(encoding='utf-8'), re.M) for p in modules}
assert sum(k in {'theorem', 'lemma'} for d in ds.values() for k, _ in d) == 33
assert sum(k in {'def', 'abbrev'} for d in ds.values() for k, _ in d) == 12
assert sum(len(d) for d in ds.values()) == 45
print(json.dumps({'prepared_modules': len(modules), 'declarations': 45}))
