from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-nested-dual-density-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-nested-dual-density-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-nested-dual-density'", "PREFIX = 'round-nested-recursion'")
source = source.replace("OLD = 'round-joint-localization'", "OLD = 'round-nested-dual-density'")
modules = ['Hindman168/NestedMixedDualRecursion.lean', 'Hindman168/NestedMixedDualCoefficientStructure.lean',
           'Hindman168/NestedMixedDualUniformThreshold.lean']
components = [
    'The actual lower recursive coefficient and the product of its two shifted directions are now defined. Their unit bounds are proved, and the zero-degree coefficient is identified exactly with the constant one. A genuine outer dual whose distinguished singleton input is a second-direction actual dual has an exact two-level finite Haar expansion after subgroup shifts n and m, with the shifted coefficient product and translated inner singleton input displayed. Every genuine nested generator supplies actual unit inputs retaining both factors and this exact expansion. Each shifted lower coefficient lies in a positive-degree target factor under an explicit positive-lower-degree containment premise, with the zero-degree branch discharged by constant-one membership. Under the two explicit lower intersection containments, the actual double coefficient is unit bounded and target structured for arbitrary shifts selected by stage and original cell. A uniform eventual positive Gowers threshold consequently tests every pair of double coefficients against every actual unit test. The lower containments remain premises to be discharged by the higher-order concatenation induction; no full concatenation theorem is claimed here.'
]
old_gap = ' The actual two-level recursive coefficient expansions still need to be connected to the higher-order concatenation induction.'
assert old_gap in previous.REMAINING
remaining = previous.REMAINING.replace(old_gap,
    ' ' + components[0] + ' The exact two-level expansion and uniform paired-coefficient testing still need to be connected through the weighted Cauchy-Schwarz estimate, subgroup-sum Haar averaging and next-order Gowers moment to the higher-order concatenation induction.')
source = re.sub(r'^MODULES = .*$', 'MODULES = ' + repr(modules), source, flags=re.M)
source = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), source, flags=re.M)
source = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), source, flags=re.M)
counts = {'1118': '1121', '1103': '1106', '5226': '5236', '1121': '1124', '1112': '1115'}
source = re.sub(r'\b(?:1118|1103|5226|1121|1112)\b', lambda m: counts[m.group()], source)
source = source.replace('assert len(names) == len(set(names)) == 15', 'assert len(names) == len(set(names)) == 10')
source = source.replace('for kind, _ in values) == 11', 'for kind, _ in values) == 8')
source = source.replace("'theorem_count': 11", "'theorem_count': 8")
source = source.replace('and len(names) == 15', 'and len(names) == 10')
for old_text, new_text in [
    ('new_theorems=11', 'new_theorems=8'), ('new_definitions=4', 'new_definitions=2'),
    ('new_axiom_reports=15', 'new_axiom_reports=10'),
    ('new_theorem_count=11', 'new_theorem_count=8'), ('new_selected_report_count=15', 'new_selected_report_count=10')
]:
    source = source.replace(old_text, new_text)
review = [
    'PROGRESS. The nested-dual-density round was rechecked against authoritative source hashes, terminal build and kernel output before edits. This increment changes no retained proof source or axiom set.',
    'The lower recursive coefficient is defined by the actual mixed dual with paired shifted outer inputs. Its unit bound requires only nonroot input unit bounds, using nonemptiness of the successor image and of the inserted-zero vertex. The zero-degree branch is proved by the exact empty nonroot vertex product. The ordinary decidable finite-set equality is kernel checked; no native decision procedure is used.',
    'The double coefficient is the product of the first lower coefficient evaluated at x+m and the second lower coefficient evaluated at x+h. The shift positions are fixed by the actual two-level expansion, not chosen for convenience. Its unit bound follows from the two independently verified lower coefficient bounds.',
    'For an actual outer dual with its distinguished singleton input equal to an actual second-direction dual, the previously verified subgroup-shift recursion is applied first at x+m and then at x+h. Haar linearity pulls the first coefficient inside the second average. Commutativity of multiplication gives the exact product coefficient and translated inner singleton input. This holds for arbitrary finite subgroups and for zero lower degrees. No unit or structure premise is needed for this algebraic identity.',
    'The target-structure helper separates zero and positive lower degrees. At zero it constructs the actual constant-one family and proves target membership with the genuine target dual hull. At positive degree it applies the audited recursive localization theorem and the explicitly displayed lower-intersection containment, then the audited translation closure in the positive-degree target factor. Shifts may vary by stage and cell.',
    'The two target-structured lower coefficients are constructed with precisely the evaluation shifts m and h required by the exact expansion. Their actual product is represented by the verified weighted Haar multiplier. Positive-degree target multiplication closure yields its target membership, and pointwise evaluation is matched exactly to the double coefficient definition.',
    'A genuine nested family at the singleton vertex supplies its outer actual-family witness and the inner joint-dual witness. Both witnesses retain actual unit inputs and both original factor memberships. Their defining pointwise identities discharge the premises of the exact double expansion, giving the expansion for every stage, original cell and both subgroup shifts.',
    'The uniform threshold proof considers every dependent selected quadruple of ambient shift functions. The actual target-structure theorem supplies its unit representative, which is identified with the canonical weighted bounded family by subtype extensionality. The audited finite-product threshold theorem is applied with two such coefficient families, giving one eventual positive threshold for all paired shifts and all unit tests.',
    'The two lower intersection containments are explicit premises, conditional on positive lower degrees. They are not postulates, global instances or hidden hypotheses replacing a missing concatenation proof. In a concatenation induction they still require proofs at smaller total degree; this increment does not claim that those containments have been discharged.',
    'Each new module is individually compiled before registry changes. Full terminal build and complete selected kernel-axiom checks, exact root and registry counts, new object freshness and retained source/hash checks are required before this record is accepted.',
    'This follows Section 7 equations (46)-(50) in the finite-subgroup setting: Haar invariance makes the representation exact. The proof only needs a genuine second-direction dual at the distinguished outer singleton input, as supplied by the preceding nested density equality. All other outer inputs retain the other factor for lower-coefficient localization.',
    'Eight theorems and two definitions are audited. Weighted correlation Cauchy-Schwarz, subgroup-sum Haar reduction, next-order moment integration and discharge of the concatenation induction remain. Full qualitative Bessel, inverse correlator existence, replica and interval integration and StrongConjecture remain unproved.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://arxiv.org/html/1603.07815v4', reference_scope='Section 7 equations (46)-(50), actual subgroup case')\n"
) + source[end:]
Path('round-nested-recursion-audit.py').write_text(source, encoding='utf-8')
print('Prepared three-module audit: eight theorems and two definitions.')
