from pathlib import Path
import ast
import json
import re

modules = ['Hindman168/' + n + '.lean' for n in [
    'AlignmentColoringCompactness', 'AlignmentFreeNilpotent',
    'AlignmentMonomialWords', 'AlignmentFiniteRecurrenceTransfer',
    'AlignmentIntegralMonomialWords', 'AlignmentTargetAlternatives',
    'AlignmentJumpTemplates']]
components = [
    'The actual finite recurrence cylinders are open in the full coloring space. Compactness proves a finite alternative table with only positive parameters from explicit pointwise recurrence, including empty-word-list and empty-coloring-space cases. No recurrence existence is inferred from compactness alone.',
    'The free group quotient by mathlib lowerCentralSeries s has its own lower central series zero at s. Every generator assignment into a group with the same step bound factors through the actual quotient and maps each free generator exactly to its assignment. A countable alphabet gives a countable quotient.',
    'Ordered positive-degree monomial words preserve concatenation and transport exactly through group homomorphisms. Their parameter-zero value is identity. One finite alternative table therefore transfers to every interpretation of the generators and to arbitrary left actions. Inverting the words and coloring proves the paper handedness conversion.',
    'The actual integral inflated rational-letter words are exactly monomial words, both directly and through a finite alphabet map. At positive parameters the actual updated-scale words have the same interpretation. The same free-group alternatives supply all leading palette comparisons at the target block, using its exact fixed product under the compensating scale update.',
    'Each free nilpotent jump has a signed-word representative. Every finite table has a finite signed-word lift retaining its positive parameters and covering exactly the original table. Under actual integral old-scale exponents its interpreted jump is exactly the original rational-letter word, including signed inverses. A target now has a finite list of actual word-template jumps chosen before scales, generators, palettes and centers, conditional only on the explicitly stated polynomial recurrence premise.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. '
    'Conditional Prediction includes actual admissible parameters, finite positive scale-list closure, all scale/color indices, globally unit-range common native observables and actual fixed-ultrafilter calibration and complete count limits. '
    'Alignment has exact compensating updates, positive exponents, integral word inflation and predecessor preservation. From explicit pointwise free-nilpotent monomial recurrence, compactness and the universal quotient now prove uniform finite signed word-template choices for actual target palette requirements before numerical scale and generator values. '
    'The genuine nilpotent polynomial recurrence existence proof, full backward/forward finite plan assembly, and positive-probability integer Alignment realization remain unproved. '
    'Final ordered positive rapidly separated monochromatic extraction is also incomplete. No unavoidable blocker is established. '
    'A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The previous alignment-scale-updates round was terminal-successfully rechecked and the authoritative 1290-source manifest copied before new source edits. Retained proof sources are fixed.',
    'The OpenAI 08_alignment uniform finite version is implemented by compactness of Color^H, where only Color is finite. Coordinate equality is an open cylinder and each success condition is a finite intersection. The complete coloring space is covered by the explicit pointwise recurrence premise. Filtering the finite subcover to positive parameters keeps every successful coloring covered.',
    'Mathlib LCS zero is the whole group, so quotienting at index s corresponds to gamma_(s+1) in the paper. Surjectivity of the actual quotient homomorphism, functoriality of LCS and its exact kernel prove the step bound. The interpretation homomorphism is constructed using the proved kernel inclusion, not an assumed universal-property axiom.',
    'The action, target and signed-word choice theorem statements all quantify one finite table before every group, group structure, state space, action, scale, generator interpretation, palette and center. An initial weaker quantifier order was corrected before registration. Pulling back an actual coloring and pushing the exact ordered word through the homomorphism prove transfer. Pulling back a palette along g acting on x retains wJx and requires no commutativity or fixing of old targets.',
    'The primary Zorin-Kranich arXiv:1206.0287v4 Corollary 3.7 and proof were reviewed at https://arxiv.org/html/1206.0287v4 . That theorem uses left translates of ordered VIP expressions. The separate Lean inversion theorem proves the handedness conversion. This round does not formalize its VIP closure, stretched filtration or PET recurrence existence; these remain explicit missing work.',
    'Actual prior integer letter exponents identify inflated words with monomial powers k^lambda.toNat. Finite alphabet maps retain repeated and signed letters without identifying distinct numerical generators. No floor approximation is substituted for integrality. The target palette index is fixed by the actual scale update and leading indices are bundled in a genuinely finite palette type.',
    'Abstract free-group jumps alone would not meet predecessor word-list budgets. Finite signed representatives are therefore proved and transported to the original rational-letter word evaluation. The representative table depends only on the abstract alternatives. Exact old-scale integral exponents and signed inverse identities establish the jump equality used by the actual target theorem.',
    'Seven new modules contain twenty-one theorems and seven definitions or abbreviations, with twenty-eight selected kernel reports. Full build and axiom output must finish without errors or warnings; no new axioms, proof holes or resource options are permitted. Retained source hashes and full axiom sets must remain unchanged except root imports and registry.',
    remaining
]
source = Path('round-alignment-scale-updates-audit.py').read_text(encoding='utf-8')
numbers = {'1285': '1290', '1290': '1297', '1272': '1279', '1281': '1288',
    '5705': '5733', '23': '21', '35': '28', '12': '7', '5': '7'}
source = re.sub(r'\b(?:' + '|'.join(numbers) + r')\b',
    lambda m: numbers[m.group()], source)
source = source.replace('path[:-7]', 'path[:-5]')
source = source.replace('new_structures=1', 'new_structures=0')
source = source.replace("for p in MODULES) == 1", "for p in MODULES) == 0")
values = {'PREFIX': 'round-alignment-finite-alternatives', 'OLD': 'round-alignment-scale-updates',
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
source = source.replace(
    "reference_scope='08_alignment exact scale updates, positive exponents, ordered word inflation, predecessor requirements and finite denominator clearing'",
    "reference_scope='08_alignment uniform finite nilpotent word choices by compactness, free quotient, integral monomial interpretation and signed jump representatives'")
focused = '''def check_focused():
    results = obj(PREFIX + '-focused-results.json')
    assert [r['module'] for r in results] == MODULES
    for r in results:
        assert r['terminal'] and r['exit_code'] == 0
        assert r['command'] == ['lake', 'env', 'lean', '-DautoImplicit=false', r['module']]
        assert digest(r['module']) == r['source_sha256']
        assert digest(r['log']) == r['log_sha256']
        assert not Path(r['log']).read_bytes().strip()


'''
source = source.replace('def register():\n', focused + 'def register():\n    check_focused()\n', 1)
source = source.replace('def check():\n', 'def check():\n    check_focused()\n', 1)
anchor = "    prior = read('Hindman168/PrincipalPredictionModels.lean')\n"
assert source.count(anchor) == 1
scope_checks = '''    for path, name, existential in [
        ('Hindman168/AlignmentFiniteRecurrenceTransfer.lean', 'alignment_uniform_action_alternatives', '∃ alternatives'),
        ('Hindman168/AlignmentTargetAlternatives.lean', 'alignment_target_finite_alternatives', '∃ alternatives'),
        ('Hindman168/AlignmentJumpTemplates.lean', 'alignment_target_finite_word_choices', '∃ choices')]:
        statement = read(path).split('theorem ' + name, 1)[1].split(' := by', 1)[0]
        assert statement.index(existential) < statement.index('∀ (G : Type')
        assert '[Group G]' in statement and '[MulAction G X]' in statement
        assert '{G X' not in statement
'''
source = source.replace(anchor, scope_checks + anchor, 1)
ast.parse(source)
Path('round-alignment-finite-alternatives-audit.py').write_text(source, encoding='utf-8')
ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+(\w+)',
    Path(p).read_text(encoding='utf-8'), re.M) for p in modules}
assert sum(k in {'theorem', 'lemma'} for d in ds.values() for k, _ in d) == 21
assert sum(k in {'def', 'abbrev'} for d in ds.values() for k, _ in d) == 7
print(json.dumps({'modules': 7, 'theorems': 21, 'definitions': 7, 'reports': 28,
    'baseline_hashes': 1290, 'current_modules': 1279, 'current_reports': 5733}))
