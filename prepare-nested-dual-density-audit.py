from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-joint-localization-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-joint-localization-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-joint-localization'", "PREFIX = 'round-nested-dual-density'")
source = source.replace("OLD = 'round-localized-intersection-density'", "OLD = 'round-joint-localization'")
modules = ['Hindman168/MixedDualInputContinuity.lean', 'Hindman168/NestedMixedDualSpan.lean',
           'Hindman168/NestedMixedDualDensity.lean']
components = [
    'The actual mixed dual is now a linear contraction in any single nonroot input when its other nonroot inputs are unit bounded. The replaced input needs only L2 boundedness, not a pointwise unit bound. The contraction preserves the original weighted finite Haar norm and passes to Hilbert distances along every ultrafilter. Genuine nested dual families are defined by requiring one distinguished nonroot input of a joint first-direction dual to be an actual joint second-direction dual. Their closed Hilbert span is proved equal to the original factor intersection for positive degrees and tail-containing ultrafilters. The proof inserts actual finite second-direction dual approximants through the contraction and uses linearity to keep the output in the nested generator span. Consequently every intersection vector has actual uniformly bounded algebraic-span approximants of genuine nested duals, with both original factor memberships retained at the inputs and all original cell weights unchanged.'
]
old_gap = ' The two-level approximation and nested recursive coefficient expansions still need to be connected to the higher-order concatenation induction.'
assert old_gap in previous.REMAINING
remaining = previous.REMAINING.replace(old_gap,
    ' ' + components[0] + ' The actual two-level recursive coefficient expansions still need to be connected to the higher-order concatenation induction.')
source = re.sub(r'^MODULES = .*$', 'MODULES = ' + repr(modules), source, flags=re.M)
source = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), source, flags=re.M)
source = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), source, flags=re.M)
counts = {'1115': '1118', '1100': '1103', '5211': '5226', '1118': '1121', '1109': '1112'}
source = re.sub(r'\b(?:1115|1100|5211|1118|1109)\b', lambda m: counts[m.group()], source)
source = source.replace('assert len(names) == len(set(names)) == 20', 'assert len(names) == len(set(names)) == 15')
source = source.replace('for kind, _ in values) == 16', 'for kind, _ in values) == 11')
source = source.replace("'theorem_count': 16", "'theorem_count': 11")
source = source.replace('and len(names) == 20', 'and len(names) == 15')
for old_text, new_text in [
    ('new_theorems=16', 'new_theorems=11'), ('new_definitions=3', 'new_definitions=4'),
    ('new_instances=1', 'new_instances=0'), ('new_axiom_reports=20', 'new_axiom_reports=15'),
    ('new_theorem_count=16', 'new_theorem_count=11'), ('new_selected_report_count=20', 'new_selected_report_count=15')
]:
    source = source.replace(old_text, new_text)
review = [
    'PROGRESS. The joint-localization round was rechecked before edits. This increment adds only new proof modules; retained proof source hashes and registered axiom sets remain unchanged.',
    'The exact input-average identity isolates a distinguished nonroot input using the finite product with that vertex erased. Nonroot status is explicit; without it the original dual ignores the chosen input and the linear-map construction would not apply.',
    'With all other nonroot inputs unit bounded, finite Haar Cauchy-Schwarz discards their product. Ambient translation invariance identifies the remaining averaged input square with its original finite Haar square. Summing with the original nonnegative cell weights yields the weighted L2 contraction. No normalization of the cell probabilities or pointwise bound on the replaced input is needed for this operator.',
    'The replacement operator is an actual linear map on L2-bounded families, with pointwise addition and scalar multiplication verified using the isolated input identity. The contraction bounds its family norm and passes to Hilbert distances by the previously verified norm-square limits. This does not assume a bounded representative for an arbitrary completed Hilbert vector.',
    'Nested generators are actual joint first-direction dual families whose distinguished nonroot input is itself a genuine joint second-direction dual. All outer nonroot inputs retain both factor memberships. The inner joint dual definition supplies actual unit inputs retaining both factors as well. The nested closed span is contained in the original intersection by subset inclusion in the audited joint generator span.',
    'For a joint second-direction generator inserted into the first-direction input operator, unit boundedness and factor-intersection membership follow from the audited joint-family results with the factors interchanged. The positive first degree is explicitly required for this use. The resulting substituted actual family is shown to have a genuine nested witness.',
    'The distinguished original outer input lies in both factors because it is nonroot. The audited joint-density theorem with swapped factors provides actual algebraic-span approximants in the second direction. Their pointwise bound may exceed one or vary with the approximation; the new contraction is valid without a bound on this replaced input.',
    'The composed linear map from actual families to the Hilbert completion takes the entire algebraic span of the second-direction joint generators into the nested closed span. The actual original outer dual is identified exactly with the operator applied to its original distinguished input. L2 contraction controls the approximation error, proving membership in the closed nested span.',
    'Closure and algebraic span then extend this membership from joint outer generators to their entire closed span. The audited equality of that joint span with the original factor intersection yields the new nested-span equality. A generic unit-generator approximation theorem supplies actual uniformly bounded nested algebraic-span approximants for every intersection vector.',
    'Every new module was compiled separately before registry changes. The full build, complete selected kernel-axiom output, retained hash checks and exact registry/import comparisons are required before recording this round. Compilation errors during development are not used as verification evidence.',
    'This proves the single distinguished input substitution needed for the two-level Section 7 approximation. It does not assert simultaneous substitutions at all vertices, actual double recursive coefficient formulas, or the higher-order concatenation induction. Those next proof steps remain explicit work.',
    'Eleven theorems and four definitions are audited. Genuine nested generator-density is now proved, while full higher-order concatenation, qualitative Bessel, inverse correlator existence and the original StrongConjecture remain unproved.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://arxiv.org/html/1603.07815v4', reference_scope='Section 7 two-level actual dual approximation')\n"
) + source[end:]
Path('round-nested-dual-density-audit.py').write_text(source, encoding='utf-8')
print('Prepared three-module audit: eleven theorems and four definitions.')
