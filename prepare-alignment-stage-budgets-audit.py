from pathlib import Path
import ast
import json
import re

modules = ['Hindman168/' + n + '.lean' for n in [
    'AlignmentFiniteWordAlphabet', 'AlignmentMonomialRecurrenceInput',
    'AlignmentChoicePredecessors', 'AlignmentStageAdvance',
    'AlignmentScalePaths', 'AlignmentPlanFiniteScales']]
components = [
    'Every actual finite rational-letter word family has an explicit finite alphabet. Encoding into the subtype of occurring letters and decoding preserve the complete ordered word and the exact finite family. The still unproved monomial recurrence input is stated on finite alphabets and palettes. Its proved consequence gives actual rational-letter target choices uniformly before all groups, actions, scales, integral exponents and centers.',
    'Predecessor leading and word budgets are finite unions over every alternative. One requirement on these unions preserves the original comparison for every chosen positive update and jump. Positive input leading indices remain positive throughout the backward budgets. The ordered action and actual compensating scales are retained.',
    'A proved forward-stage theorem simultaneously establishes its own target, retains positive scales and preserves all previously specified target comparisons. The finite table is quantified before every group, state space, action, incoming scale, generator, palette and center. The recurrence, local integrality and predecessor requirements remain explicit inputs; no complete multi-target or multi-pivot recursion is asserted.',
    'An actual finite stage schedule has finite rational scale frontiers and an explicit catalogue of all incoming, intermediate and terminal tuples. All choices are represented by the original compensating updates. Positivity, concatenation, monotonicity and prefix coverage are proved, so every stage uses a tuple in the finite catalogue.',
    'All enumerated path scales and any prescribed finite letter set share one positive integer denominator. The actual finite palette index catalogue is positive for positive incoming tuples, positive choices and positive leading factors. Enlarging it by every subset product of every terminal tuple gives the exact FiniteScaleClosure required by Prediction, including all consulted intermediate palette indices.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional Prediction includes actual admissible parameters, finite positive scale-list closure, all scale/color indices, globally unit-range common native observables and actual fixed-ultrafilter calibration and complete count limits. '
    'Conditional Alignment now gives actual finite target word choices, all-alternative predecessor budgets and simultaneous forward-stage advancement; finite schedules have proved complete scale catalogues, common denominators and positive Prediction palette closure. '
    'HasAlignmentMonomialRecurrence is an explicit unproved input. Its genuine nilpotent recurrence existence proof, full backward/forward construction across all targets and pivots, finite auxiliary slot planning and positive-probability integer Alignment realization remain unproved. '
    'Final ordered positive rapidly separated monochromatic extraction is also incomplete. No unavoidable blocker is established. '
    'A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The previous alignment-finite-alternatives round was terminal-successfully rechecked. The authoritative 1297-source manifest was copied before new proof edits as round-alignment-pivot-plans-baseline.json and retained identically under the current round name. All retained proof sources remain fixed.',
    'The finite alphabet is constructed from the exact biUnion of every word toFinset. Attached-list encoding retains repeated letters and order. Both individual decode and complete finite-family decode are proved, so no theorem for a surrogate word family is substituted for the actual rational words.',
    'HasAlignmentMonomialRecurrence is a Prop definition, not an axiom or a theorem asserting existence. It universally quantifies finite alphabets, finite palettes, positive degrees and actual free step-s groups. The actual target theorem explicitly assumes it and uses the already proved exact signed-word table. Its finite alphabet is countable by the retained quotient countability theorem, matching the paper citation scope.',
    'Each old budget is the actual finite union over all possible next choices. Exact subset inclusions reduce the union requirement to the retained ordered predecessor preservation theorem. Leading positivity is proved from positive choices and the actual finite product of positive rational multipliers, including empty blocks.',
    'The stage theorem preserves arbitrary finite previous target sets and palette maps, with no action commutativity or jump-fixing premise. One selected choice establishes the new target and all old targets simultaneously. Local old-scale integrality remains explicit; the denominator theorem supplies it once a complete finite schedule and letter set have been constructed.',
    'Scale paths enumerate each finite stage choice at the exact current tuple, rather than replacing the updates by a scalar bound or selecting an already successful path. Separate catalogues retain every intermediate tuple and the terminal frontier. Concatenation and prefix containment ensure common denominators can be chosen before execution. This round proves these facts for a fixed pivot; plans at different pivots and future-multiplier terminal budgets are still missing.',
    'The palette catalogue is the actual a times block product at every enumerated tuple and every listed block and leading factor. Its enlargement contains the complete terminal subset-product family and proves FiniteScaleClosure on the actual frontier. Positive hypotheses are proved through the original scale updates. No native model or positive recurrence probability is selected by these catalogue lemmas.',
    'Six new modules contain twenty-seven theorems and twelve definitions or abbreviations, with thirty-nine selected kernel reports. New modules use no resource options, proof holes, unsafe implementation or new axioms. Full build, full kernel audit and retained-source/dependency comparisons must finish successfully before recording progress.',
    remaining
]
source = Path('round-alignment-finite-alternatives-audit.py').read_text(encoding='utf-8')
replacements = {
    "len(baseline['files']) == 1290": "len(baseline['files']) == 1297",
    "'baseline_hash_count': 1290": "'baseline_hash_count': 1297",
    'len(set(names)) == 28': 'len(set(names)) == 39',
    "for values in ds.values() for kind, _ in values) == 21": "for values in ds.values() for kind, _ in values) == 27",
    "for values in ds.values() for kind, _ in values) == 7": "for values in ds.values() for kind, _ in values) == 12",
    "'theorem_count': 21, 'selected_report_count': 28": "'theorem_count': 27, 'selected_report_count': 39",
    "names == registration['names'] and len(names) == 28": "names == registration['names'] and len(names) == 39",
    'len(own) == 1279': 'len(own) == 1285', 'len(actual) == 5733': 'len(actual) == 5772',
    "len({f['path'] for f in files}) == 1297": "len({f['path'] for f in files}) == 1303",
    'new_theorems=21, new_definitions=7, new_structures=0, new_instances=0, new_axiom_reports=28':
        'new_theorems=27, new_definitions=12, new_structures=0, new_instances=0, new_axiom_reports=39',
    'hindman_module_count=1279': 'hindman_module_count=1285',
    'selected_axiom_report_count=5733, source_scan_module_count=1288':
        'selected_axiom_report_count=5772, source_scan_module_count=1294',
    'new_module_count=7, new_theorem_count=21': 'new_module_count=6, new_theorem_count=27',
    'new_selected_report_count=28': 'new_selected_report_count=39',
    "reference_scope='08_alignment uniform finite nilpotent word choices by compactness, free quotient, integral monomial interpretation and signed jump representatives'":
        "reference_scope='08_alignment finite alphabet, all-alternative predecessor budgets, simultaneous stage advancement, finite scale paths and uniform denominator/palette planning'"
}
pattern = re.compile('|'.join(re.escape(s) for s in sorted(replacements, key=len, reverse=True)))
for before in replacements:
    assert before in source, before
source = pattern.sub(lambda m: replacements[m.group()], source)
values = {'PREFIX': 'round-alignment-stage-budgets', 'OLD': 'round-alignment-finite-alternatives',
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
scope = '''    for path, name in [
        ('Hindman168/AlignmentMonomialRecurrenceInput.lean', 'alignment_actual_target_choices'),
        ('Hindman168/AlignmentStageAdvance.lean', 'alignment_stage_advance')]:
        statement = read(path).split('theorem ' + name, 1)[1].split(' := by', 1)[0]
        assert statement.index('∃ choices') < statement.index('∀ (G : Type')
        assert 'hrec : HasAlignmentMonomialRecurrence s' in statement
        assert '(Int.castRingHom ℚ).range' in statement
    recurrence = read('Hindman168/AlignmentMonomialRecurrenceInput.lean')
    assert 'def HasAlignmentMonomialRecurrence' in recurrence
    assert not re.search(r'(?:theorem|lemma)\\s+HasAlignmentMonomialRecurrence', recurrence)
'''
assert source.count(anchor) == 1
source = source.replace(anchor, scope + anchor, 1)
ast.parse(source)
Path('round-alignment-stage-budgets-audit.py').write_text(source, encoding='utf-8')
focused = Path('check-alignment-finite-alternatives.py').read_text(encoding='utf-8')
focused = focused.replace("prefix = 'round-alignment-finite-alternatives'", "prefix = 'round-alignment-stage-budgets'")
Path('check-alignment-stage-budgets.py').write_text(focused, encoding='utf-8')
ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+(\w+)',
    Path(p).read_text(encoding='utf-8'), re.M) for p in modules}
assert sum(k in {'theorem', 'lemma'} for d in ds.values() for k, _ in d) == 27
assert sum(k in {'def', 'abbrev'} for d in ds.values() for k, _ in d) == 12
print(json.dumps({'modules': 6, 'theorems': 27, 'definitions': 12, 'reports': 39,
    'baseline_hashes': 1297, 'current_modules': 1285, 'current_reports': 5772}))
