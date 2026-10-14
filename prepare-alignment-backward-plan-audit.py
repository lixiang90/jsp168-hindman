from pathlib import Path
import ast
import json
import re

modules = ['Hindman168/' + n + '.lean' for n in [
    'AlignmentPivotRequests', 'AlignmentBackwardPlan',
    'AlignmentPivotExecution', 'AlignmentUniformPivotPlan']]
components = [
    'Actual typed pivot requests retain the exact target tail, leading and ordered word budgets. Their all-choice predecessors have the same target, proved positive leading factors when the input ones are positive, and exact palette preservation under every admitted update and jump. A stage whose target is any prescribed request exists from the still explicit monomial recurrence input, uniformly over every group, action and numerical scale.',
    'A complete backward plan for any finite list of pivot requests is constructed by strong induction on request count. Its exact fitting predicate records the last target and every strengthened predecessor request. The number of stages equals the number of terminal requests. The plan is stored last-stage first and its reverse gives the actual forward schedule.',
    'The backward plan executes forward on actual rational scales and actual ordered word actions. An explicit reachability trace ties its final scale and center to the input scale and center through admitted choices at every stage. Every intermediate tuple belongs to the complete pre-enumerated catalogue. Each chosen positive update establishes its own target and preserves all previous requests, including repeated target blocks with different budgets. All final requested comparisons and scale positivity hold simultaneously.',
    'All stage target alphabets across the complete plan share one positive denominator at every possible incoming, intermediate and terminal tuple. The final uniform pivot theorem chooses the plan before any incoming finite numerical scale family, then chooses its common denominator before every group, state space, action, generator assignment, palette and initial center. It proves complete finite-plan existence and execution at a fixed pivot, conditional on HasAlignmentMonomialRecurrence.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional Prediction includes actual admissible parameters, finite positive scale-list closure, all scale/color indices, globally unit-range common native observables and actual fixed-ultrafilter calibration and complete count limits. '
    'Conditional Alignment now has a complete backward-built and forward-executed finite plan for every prescribed finite request list at one pivot, with exact predecessor budgets, positive scales, complete path catalogues and a uniform common denominator. The plan precedes incoming numerical scales, and the denominator precedes all group actions and palettes. '
    'HasAlignmentMonomialRecurrence remains an explicit unproved input. Its genuine nilpotent recurrence existence proof, decreasing-pivot future-multiplier planning, finite auxiliary slot planning and positive-probability integer Alignment realization remain unproved. '
    'Final ordered positive rapidly separated monochromatic extraction is also incomplete. No unavoidable blocker is established. '
    'A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The previous alignment-stage-budgets round was terminal-successfully rechecked and its authoritative 1303-source manifest copied before new proof edits. All retained proof sources remain fixed.',
    'Pivot requests carry the actual Fin n tail, its before-pivot proof, leading rational factors and ordered rational-letter words. Typed stages carry their actual target and finite choices. Request semantics is exactly the retained palette requirement at insert i tail. Predecessors keep the target and replace only the two finite budgets.',
    'Backward construction uses strong induction on request-list length. Ordinary induction on a particular unchanged prefix would not justify applying the hypothesis to a different strengthened budget list. The proof explicitly recurses on the mapped predecessor list, whose length is the strictly shorter prefix length. No arbitrary assumed plan or assumed predecessor satisfiability is used.',
    'The fitting predicate is a recursive Prop definition and retains the exact terminal list. It proves the same number of stages and targets. Last-stage-first storage is converted to a forward schedule by list reverse and the exact reverse-cons/append identity.',
    'Forward execution inducts on the constructed backward plan. Its recursive call uses every strengthened prior request and actual state. Prefix scale-catalogue containment supplies the same previously chosen denominator at the recursive state. The final stage picks its actual successful word jump; the retained all-choice preservation theorem protects each prior request through that same jump. Repeated target blocks require no distinctness assumption.',
    'Terminal scales belong to the actual frontier of the whole schedule by its append identity and the explicit scale-step membership theorem. The final theorem also exposes positivity of every option in the plan. An initially weaker endpoint statement did not reference the starting center; it was strengthened before registration to include an explicit recursive reachability trace. Each trace step uses a member of the actual finite stage table and the original old-scale ordered word action.',
    'The common denominator covers the finite union of all stage target alphabets at every enumerated scale. Signed jump interpretation already follows from integrality of those alphabets. The final theorem explicitly quantifies one plan before every incoming finite scale family, then one positive denominator before all groups, state spaces, actions, numerical generators, palettes and centers. This round completes fixed-pivot finite planning only; all-pivot future budgets and integer positive probability remain absent.',
    'Four new modules contain nine theorems, eight definitions and two data structures. Seventeen selected reports cover all theorems and definitions; structure field semantics is exposed by these reports. No new axioms, proof holes, unsafe implementation or resource options are allowed. Full build, kernel audit and retained-source/dependency comparisons must finish successfully before recording progress.',
    remaining
]
source = Path('round-alignment-stage-budgets-audit.py').read_text(encoding='utf-8')
replacements = {
    "len(baseline['files']) == 1297": "len(baseline['files']) == 1303",
    "'baseline_hash_count': 1297": "'baseline_hash_count': 1303",
    'len(set(names)) == 39': 'len(set(names)) == 17',
    "for values in ds.values() for kind, _ in values) == 27": "for values in ds.values() for kind, _ in values) == 9",
    "for values in ds.values() for kind, _ in values) == 12": "for values in ds.values() for kind, _ in values) == 8",
    "'theorem_count': 27, 'selected_report_count': 39": "'theorem_count': 9, 'selected_report_count': 17",
    "names == registration['names'] and len(names) == 39": "names == registration['names'] and len(names) == 17",
    'len(own) == 1285': 'len(own) == 1289', 'len(actual) == 5772': 'len(actual) == 5789',
    "len({f['path'] for f in files}) == 1303": "len({f['path'] for f in files}) == 1307",
    'new_theorems=27, new_definitions=12, new_structures=0, new_instances=0, new_axiom_reports=39':
        'new_theorems=9, new_definitions=8, new_structures=2, new_instances=0, new_axiom_reports=17',
    'hindman_module_count=1285': 'hindman_module_count=1289',
    'selected_axiom_report_count=5772, source_scan_module_count=1294':
        'selected_axiom_report_count=5789, source_scan_module_count=1298',
    'new_module_count=6, new_theorem_count=27': 'new_module_count=4, new_theorem_count=9',
    'new_selected_report_count=39': 'new_selected_report_count=17',
    'for p in MODULES) == 0': 'for p in MODULES) == 2',
    "reference_scope='08_alignment finite alphabet, all-alternative predecessor budgets, simultaneous stage advancement, finite scale paths and uniform denominator/palette planning'":
        "reference_scope='08_alignment complete fixed-pivot backward finite plan and forward execution with a uniform common denominator'"
}
pattern = re.compile('|'.join(re.escape(s) for s in sorted(replacements, key=len, reverse=True)))
for before in replacements:
    assert before in source, before
source = pattern.sub(lambda m: replacements[m.group()], source)
values = {'PREFIX': 'round-alignment-backward-plan', 'OLD': 'round-alignment-stage-budgets',
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
scope = '''    statement = read('Hindman168/AlignmentUniformPivotPlan.lean').split(
        'theorem alignment_uniform_pivot_plan', 1)[1].split(' := by', 1)[0]
    assert statement.index('∃ plan') < statement.index('∀ incoming') < statement.index('∃ q₀') < statement.index('∀ (G : Type')
    assert 'hrec : HasAlignmentMonomialRecurrence s' in statement
    assert 'alignmentScaleFrontier i (alignmentForwardOptions plan) incoming' in statement
    assert 'alignmentPivotReachable q₀ L plan b x' in statement
'''
assert source.count(anchor) == 1
source = source.replace(anchor, scope + anchor, 1)
ast.parse(source)
Path('round-alignment-backward-plan-audit.py').write_text(source, encoding='utf-8')
focused = Path('check-alignment-stage-budgets.py').read_text(encoding='utf-8')
focused = focused.replace("prefix = 'round-alignment-stage-budgets'", "prefix = 'round-alignment-backward-plan'")
Path('check-alignment-backward-plan.py').write_text(focused, encoding='utf-8')
ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+(\w+)',
    Path(p).read_text(encoding='utf-8'), re.M) for p in modules}
assert sum(k in {'theorem', 'lemma'} for d in ds.values() for k, _ in d) == 9
assert sum(k in {'def', 'abbrev'} for d in ds.values() for k, _ in d) == 8
print(json.dumps({'modules': 4, 'theorems': 9, 'definitions': 8, 'structures': 2, 'reports': 17,
    'baseline_hashes': 1303, 'current_modules': 1289, 'current_reports': 5789}))
