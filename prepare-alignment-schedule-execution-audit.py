from pathlib import Path
import ast
import json
import re

modules = ['Hindman168/' + n + '.lean' for n in [
    'AlignmentSchedulePaths', 'AlignmentScheduleDenominators',
    'AlignmentScheduleExecution', 'AlignmentCanonicalTargets']]
components = [
    'The actual relative multiplier catalogues at each planned pivot enumerate all possible incoming, intermediate and terminal global scales. A singleton-input executed pivot lands in the explicit next-step catalogue. Monotonicity supplies every stage scale to the global catalogue, and positivity of all incoming coordinates and choice parameters proves positivity of the complete state and terminal catalogues.',
    'A single positive integer denominator is chosen for the entire multi-pivot schedule before any groups, actions, generators, palettes or initial centers. It covers each stage recurrence alphabet, all admitted jump letters and every original terminal test letter at every enumerated state or final scale. No action-specific or per-pivot denominator choices are substituted.',
    'The full backward schedule now executes in order using independent per-pivot groups and initial centers. The actual recursive trace retains every fixed-pivot reachability witness, the unchanged chosen center in every final-scale request, and the shared final scale. The selected later scale product is proved a member of the precomputed future catalogue and exactly factors the final scale relative to the pivot endpoint. Future transport therefore supplies all final comparisons at the same frozen center.',
    'All adding pairs are finitely enumerated from their original Fin n fields and ordering proofs. Every pair occurs, the list has no duplicates, all nonempty target alphabets occur, and filtering by target keeps the exact fixed order. The complete canonical request family and List.finRange n remove arbitrary external requests from the final theorem. Starting scales at one, the theorem chooses the whole schedule and its common positive denominator before all model data and proves simultaneous comparisons for every target and every sublist, with one chosen center for all targets at each pivot. This finite-word theorem remains conditional on HasAlignmentMonomialRecurrence.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional Prediction includes actual admissible parameters, finite positive scale-list closure, all scale/color indices, globally unit-range common native observables and actual fixed-ultrafilter calibration and complete count limits. '
    'Conditional Alignment now has full backward planning and actual forward execution at all canonical pivots and targets, one common positive integer denominator covering all stage, jump and terminal letters, complete positive global scale catalogues and exact final-scale comparisons at each frozen pivot center. '
    'HasAlignmentMonomialRecurrence remains an explicit unproved input. Its genuine nilpotent recurrence existence proof, complete global positive palette-index closure and finite auxiliary prefix-slot planning, the integer residue/polynomial array realization and positive-probability Alignment bounds remain unproved. '
    'Final ordered positive rapidly separated monochromatic extraction is also incomplete. No unavoidable blocker is established. '
    'A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The preceding future-scales round was rechecked successfully; its authoritative 1313-source manifest was copied before new proof edits. It had completed backward planning, while explicitly leaving combined forward execution and one global denominator open.',
    'The global finite scale step multiplies each actual incoming tuple by each complete ones-input pivot multiplier. The retained singleton factor theorem proves every actual executed pivot endpoint lies in that catalogue. The global state catalogue includes all actual fixed-pivot stage scales before moving to the next global step. Its positivity follows from the genuine positive stage choice parameters.',
    'The finite rational scalar set includes every stage target letter, every admitted jump letter and every original request letter. Clearing all these scalars at the union of global intermediate and terminal scales supplies one common integer before any group, action, assignment, palette or center. Including original terminal letters prevents a generator-only denominator statement from being used to claim integrality of unbudgeted final tests.',
    'Forward execution recurses on the actual ordered schedule. At each pivot the previously proved finite plan produces a reachable endpoint and one successful center. The recursive tail returns its actual chosen future multiplier and exact factorization of the final scale. Transport with that same multiplier turns all future-augmented requests into original requests at the final scale and the unchanged pivot center.',
    'The recursive outcome predicate ties every pivot jump to its input scale and input center, stores one actual successful center for all its requests, and uses one shared final scale throughout the whole tail. A separate comparison projection exposes simultaneous final comparisons for every plan in the list. The generic occurrence theorem allows repeated pivot labels; the canonical main caller uses each Fin n pivot exactly once in increasing List.finRange order.',
    'Pair finiteness is proved by injectivity into its three original finite fields; proof fields are handled by proof irrelevance. The Fintype value is local and reducible, so no global new instance is installed. Finset.univ.toList fixes an order depending on n alone. Every actual pair is present once. The finite target-tail image contains exactly targets with a nonempty pair alphabet, and its order proof is derived from a real corresponding pair.',
    'Canonical requests enumerate each target-tail subtype, and each uses all sublists of the exact ordered target pair list. Thus all subset tests are covered by the retained filtered-subset support theorem. Empty sublists are included. The final theorem proves one center per pivot that works for all target blocks and all selected sublists. The actual integer exponents are q0 times the original final-scale ratios, not assumed separate generators.',
    'This closes the common-denominator and combined forward execution gaps in the abstract finite-word construction. It does not prove monomial nilpotent recurrence existence. The remaining global palette-index closure, bounded auxiliary prefix slots, actual integer model action and positive probability loss must still be connected before a complete Alignment principle or StrongConjecture can be claimed.',
    'Four modules contain 26 theorems and 12 definitions, with all 38 declaration names selected for kernel audit. No new structures, instances, unproved axioms, proof holes, unsafe code or resource options are introduced. Strict focused checks, full build, exact selected axiom checks, unchanged retained hashes and final recheck must all terminate successfully before progress is recorded.',
    remaining
]
source = Path('round-alignment-future-scales-audit.py').read_text(encoding='utf-8')
replacements = {
    "len(baseline['files']) == 1307": "len(baseline['files']) == 1313",
    "'baseline_hash_count': 1307": "'baseline_hash_count': 1313",
    "for values in ds.values() for kind, _ in values) == 27": "for values in ds.values() for kind, _ in values) == 26",
    "for values in ds.values() for kind, _ in values) == 11": "for values in ds.values() for kind, _ in values) == 12",
    "'theorem_count': 27, 'selected_report_count': 38": "'theorem_count': 26, 'selected_report_count': 38",
    'for p in MODULES) == 1': 'for p in MODULES) == 0',
    'len(own) == 1295': 'len(own) == 1299',
    'len(actual) == 5827': 'len(actual) == 5865',
    "len({f['path'] for f in files}) == 1313": "len({f['path'] for f in files}) == 1317",
    'new_theorems=27, new_definitions=11, new_structures=1, new_instances=0, new_axiom_reports=38':
        'new_theorems=26, new_definitions=12, new_structures=0, new_instances=0, new_axiom_reports=38',
    'hindman_module_count=1295': 'hindman_module_count=1299',
    'selected_axiom_report_count=5827, source_scan_module_count=1304':
        'selected_axiom_report_count=5865, source_scan_module_count=1308',
    'new_module_count=6, new_theorem_count=27': 'new_module_count=4, new_theorem_count=26',
    "reference_scope='08_alignment exact future-scale word transport, ordered subset budgets and full backward planning across finite pivot lists'":
        "reference_scope='08_alignment common global denominator and actual multi-pivot execution for every canonical target and ordered subset test'"
}
for before in replacements:
    assert before in source, before
pattern = re.compile('|'.join(re.escape(s) for s in sorted(replacements, key=len, reverse=True)))
source = pattern.sub(lambda m: replacements[m.group()], source)
values = {'PREFIX': 'round-alignment-schedule-execution', 'OLD': 'round-alignment-future-scales',
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
scope = '''    statement = read('Hindman168/AlignmentScheduleExecution.lean').split(
        'theorem alignment_uniform_schedule', 1)[1].split(' := by', 1)[0]
    assert statement.index('∃ schedule') < statement.index('∀ incoming') < statement.index('∃ q₀') < statement.index('∀ (G : Fin n')
    assert 'hrec : HasAlignmentMonomialRecurrence s' in statement
    assert 'alignmentScheduleRealizes G X q₀ L palette requests centers schedule b final' in statement
    statement = read('Hindman168/AlignmentCanonicalTargets.lean').split(
        'theorem alignment_canonical_finite_word_plan', 1)[1].split(' := by', 1)[0]
    assert statement.index('∃ schedule') < statement.index('∃ q₀') < statement.index('∀ (G : Fin n')
    assert 'hrec : HasAlignmentMonomialRecurrence s' in statement
    assert 'schedule.map AlignmentPlannedPivot.pivot = List.finRange n' in statement
    assert '∀ i : Fin n, ∃ y : X i, ∀ T' in statement
    assert 'selected.Sublist (alignmentCanonicalTargetPairs n i T)' in statement
    assert 'alignmentScheduleRealizes G X q₀ L palette (alignmentCanonicalRequests n) centers' in statement
    assert 'alignmentScheduleLetters (alignmentCanonicalRequests n) planned' in statement
'''
assert source.count(anchor) == 1
source = source.replace(anchor, scope + anchor, 1)
ast.parse(source)
Path('round-alignment-schedule-execution-audit.py').write_text(source, encoding='utf-8')
focused = Path('check-alignment-future-scales.py').read_text(encoding='utf-8')
assert focused.count("prefix = 'round-alignment-future-scales'") == 1
focused = focused.replace("prefix = 'round-alignment-future-scales'", "prefix = 'round-alignment-schedule-execution'")
Path('check-alignment-schedule-execution.py').write_text(focused, encoding='utf-8')
ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+(\w+)',
    Path(p).read_text(encoding='utf-8'), re.M) for p in modules}
assert sum(k in {'theorem', 'lemma'} for d in ds.values() for k, _ in d) == 26
assert sum(k in {'def', 'abbrev'} for d in ds.values() for k, _ in d) == 12
assert sum(len(d) for d in ds.values()) == 38
print(json.dumps({'prepared_modules': len(modules), 'declarations': 38}))
