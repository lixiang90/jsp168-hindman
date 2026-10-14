from pathlib import Path
import ast
import json
import re

modules = ['Hindman168/' + n + '.lean' for n in [
    'AlignmentFutureWordTransport', 'AlignmentFutureRequests', 'AlignmentTerminalWords',
    'AlignmentMultiplierCatalog', 'AlignmentFuturePivotPlan', 'AlignmentAllPivotPlanning']]
components = [
    'Arbitrary rational coordinate multipliers transport actual ordered letter scalars and word values exactly. Rescaled words respect append and composition. Palette comparisons at the later scale follow from explicitly rescaled leading factors and ordered word budgets at the earlier scale, with the same actual center.',
    'A finite union of all future requests provides simultaneous transport for every admitted future tuple. Positivity of leading factors follows from positive future coordinates. Fixed ordered pair lists enumerate all subset tests by sublists; filtering any supported subset preserves its support and its prescribed order. Unit-letter rescaling gives exactly the paper coefficient d_A/d_B for every selected letter.',
    'Finite future multiplier catalogues contain products of every corresponding list of selected multipliers and preserve positivity. Actual scale updates, finite scale steps and complete fixed-pivot frontiers factor through an arbitrary incoming tuple. In particular the ones-input frontier gives the full actual relative-multiplier catalogue for every incoming scale.',
    'The uniform fixed-pivot plan is augmented by all prescribed future multipliers. It executes through the existing explicit reachability trace, then protects every requested comparison at every later scale while keeping its actual endpoint center. All legal stage properties remain available independently of its locally chosen common denominator.',
    'A full backward plan is now constructed for any finite pivot list. The later plans and their actual complete multiplier catalogues are chosen first; their finite product catalogue determines the earlier plan terminal budget. The construction records the exact requested pivot list, recursive fitting relation and legal stage property for every selected plan. It is a planning theorem, not yet a combined forward execution theorem.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional Prediction includes actual admissible parameters, finite positive scale-list closure, all scale/color indices, globally unit-range common native observables and actual fixed-ultrafilter calibration and complete count limits. '
    'Conditional Alignment includes complete backward-built and forward-executed finite plans at a fixed pivot, exact rational future transport, ordered terminal subset tests, actual relative-multiplier catalogues and full backward planning over every prescribed finite pivot list. '
    'HasAlignmentMonomialRecurrence remains an explicit unproved input. Its genuine nilpotent recurrence existence proof, a single common denominator and combined actual forward execution across all pivots, finite auxiliary slot planning and positive-probability integer Alignment realization remain unproved. '
    'Final ordered positive rapidly separated monochromatic extraction is also incomplete. No unavoidable blocker is established. '
    'A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The earlier backward-plan audit was rechecked and its authoritative 1307-source manifest copied before these proof edits. The immediately preceding eligibility inquiry changed no proof state. All retained proof files and exact selected axiom sets must remain fixed.',
    'The lost terminal-word check was recovered from the authoritative command record: terminal exit 1 for explicit tail projection and factor-one simplification. The earlier dependency build was terminal exit 0. A missing old process handle was not treated as evidence of success. These facts permit repairing the stopped source without overlapping checks.',
    'Future word transport is an exact rational identity at each ordered letter and each original floor exponent, including zero coordinates. Positivity is required separately only for positive scale and leading-factor conclusions. The proof neither commutes ordered group products nor assumes the jump fixes a center.',
    'A future request takes the finite union of leading factors and rescaled ordered words for all future tuples. This may include harmless cross-combinations, but includes each exact same-tuple budget. Monotonicity supplies that budget before exact transport at the unchanged actual center.',
    'Terminal words use sublists of one fixed ordered pair list. Every filtered supported subset has exactly its required support; no unordered product or commutative group assumption is introduced. Repeated input letters are allowed by the generic list theorem. The final main-problem pair list still requires its own prescribed finite ordering.',
    'All candidate future coordinate multipliers come from actual later fixed-pivot frontiers with ones as input. Factoring the original updates and frontier proves their catalogue applies to arbitrary earlier scales. Forall2 membership gives the actual selected product a member of the full precomputed future product catalogue.',
    'The future-stable fixed-pivot theorem retains the prior actual reachability trace and legal stage property. It chooses its plan before every incoming scale family and its positive denominator before every group, action, assignment, palette and starting center. Future transport does not change that chosen endpoint center.',
    'All-pivot existence recurses on the tail pivot list, so later plans and their catalogue are fixed before the earlier plan is selected. Its fitting predicate records exactly those later catalogues. The theorem permits any pivot list because it proves planning only. It does not yet assert actual combined execution with independent per-pivot centers or one global denominator. The pinned paper explicitly freezes each completed pivot center while processing later pivots; the remaining cross-pivot effect is only on numerical scales. Those are still genuine remaining work.',
    'Six modules contain 27 theorems, 11 definitions and one data structure, with all 38 theorem/definition names registered for kernel axiom audit. Focused checks must be warning-free at default resources; full build, kernel verification, exact retained-source checks and final recheck must all terminate successfully.',
    remaining
]
source = Path('round-alignment-backward-plan-audit.py').read_text(encoding='utf-8')
replacements = {
    "len(baseline['files']) == 1303": "len(baseline['files']) == 1307",
    "'baseline_hash_count': 1303": "'baseline_hash_count': 1307",
    'len(set(names)) == 17': 'len(set(names)) == 38',
    "for values in ds.values() for kind, _ in values) == 9": "for values in ds.values() for kind, _ in values) == 27",
    "for values in ds.values() for kind, _ in values) == 8": "for values in ds.values() for kind, _ in values) == 11",
    "'theorem_count': 9, 'selected_report_count': 17": "'theorem_count': 27, 'selected_report_count': 38",
    "names == registration['names'] and len(names) == 17": "names == registration['names'] and len(names) == 38",
    'for p in MODULES) == 2': 'for p in MODULES) == 1',
    'len(own) == 1289': 'len(own) == 1295',
    'len(actual) == 5789': 'len(actual) == 5827',
    "len({f['path'] for f in files}) == 1307": "len({f['path'] for f in files}) == 1313",
    'new_theorems=9, new_definitions=8, new_structures=2, new_instances=0, new_axiom_reports=17':
        'new_theorems=27, new_definitions=11, new_structures=1, new_instances=0, new_axiom_reports=38',
    'hindman_module_count=1289': 'hindman_module_count=1295',
    'selected_axiom_report_count=5789, source_scan_module_count=1298':
        'selected_axiom_report_count=5827, source_scan_module_count=1304',
    'new_module_count=4, new_theorem_count=9': 'new_module_count=6, new_theorem_count=27',
    'new_selected_report_count=17': 'new_selected_report_count=38',
    "reference_scope='08_alignment complete fixed-pivot backward finite plan and forward execution with a uniform common denominator'":
        "reference_scope='08_alignment exact future-scale word transport, ordered subset budgets and full backward planning across finite pivot lists'"
}
for before in replacements:
    assert before in source, before
pattern = re.compile('|'.join(re.escape(s) for s in sorted(replacements, key=len, reverse=True)))
source = pattern.sub(lambda m: replacements[m.group()], source)
values = {'PREFIX': 'round-alignment-future-scales', 'OLD': 'round-alignment-backward-plan',
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
scope = '''    statement = read('Hindman168/AlignmentFuturePivotPlan.lean').split(
        'theorem alignment_future_pivot_plan', 1)[1].split(' := by', 1)[0]
    assert statement.index('∃ plan') < statement.index('∀ incoming') < statement.index('∃ q₀') < statement.index('∀ (G : Type')
    assert 'hrec : HasAlignmentMonomialRecurrence s' in statement
    assert 'alignmentPivotReachable q₀ L plan b x' in statement
    assert '∀ d ∈ futures' in statement
    assert 'AlignmentPivotStageWorks.{u, v} s Color stage' in statement
    statement = read('Hindman168/AlignmentAllPivotPlanning.lean').split(
        'theorem alignment_all_pivot_plans_exist', 1)[1].split(' := by', 1)[0]
    assert 'hrec : HasAlignmentMonomialRecurrence s' in statement
    assert 'schedule.map AlignmentPlannedPivot.pivot = pivots' in statement
    assert 'alignmentAllPivotFits requests schedule' in statement
    assert 'AlignmentPivotStageWorks.{u, v} s Color stage' in statement
'''
assert source.count(anchor) == 1
source = source.replace(anchor, scope + anchor, 1)
ast.parse(source)
Path('round-alignment-future-scales-audit.py').write_text(source, encoding='utf-8')
focused = Path('check-alignment-backward-plan.py').read_text(encoding='utf-8')
assert focused.count("prefix = 'round-alignment-backward-plan'") == 1
focused = focused.replace("prefix = 'round-alignment-backward-plan'", "prefix = 'round-alignment-future-scales'")
Path('check-alignment-future-scales.py').write_text(focused, encoding='utf-8')
ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+(\w+)',
    Path(p).read_text(encoding='utf-8'), re.M) for p in modules}
assert sum(k in {'theorem', 'lemma'} for d in ds.values() for k, _ in d) == 27
assert sum(k in {'def', 'abbrev'} for d in ds.values() for k, _ in d) == 11
assert sum(len(d) for d in ds.values()) == 38
print(json.dumps({'prepared_modules': len(modules), 'declarations': 38}))
