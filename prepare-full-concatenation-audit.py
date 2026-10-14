from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-nested-correlation-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-nested-correlation-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-nested-correlation'", "PREFIX = 'round-full-concatenation'")
source = source.replace("OLD = 'round-nested-recursion'", "OLD = 'round-nested-correlation'")
modules = ['Hindman168/NestedMixedDualConcatenationStep.lean',
           'Hindman168/MixedDualConcatenation.lean',
           'Hindman168/MixedDualProjectionPairOrthogonality.lean']
components = [
    'The full higher-order subgroup concatenation theorem is now proved on the completed weighted Haar Hilbert space for positive degrees and tail-containing ultrafilters: V_Q(d) intersect V_R(e) is contained in V_(Q+R)(d+e-1). Null correlation of genuine nested generators first gives their membership in the next-order sum factor, using an exact unit-interval projection and a unit residual whose squared norm must vanish. The audited nested density equality extends membership to the entire closed intersection. Strong induction on total degree discharges both displayed lower containments, including the zero-degree branches through the first-order base equality. The final theorem has no unproved lower-containment premise. Orthogonality to this sum factor makes the two genuine factor projections orthogonal on the full completed Hilbert space; actual representatives consequently have vanishing weighted correlation whenever the concatenated Gowers value vanishes. All original cell probabilities and varying finite group systems are retained.'
]
remaining = previous.REMAINING.replace(
    ' The lower containments remain premises to be discharged by the higher-order concatenation induction; no full concatenation theorem is claimed here.',
    ' The local recursive lemmas display lower containments, which the subsequent full strong induction now discharges.')
gap = ' Null correlation for genuine nested generators still needs to be extended to membership in the next-order subgroup-sum closed dual space, and both lower containments discharged by the higher-order concatenation induction. Higher-order concatenation controlling dual correlations and the full qualitative Bessel theorem remain missing, as do remaining replica integration, cyclic-to-interval transfer and inverse correlator existence.'
assert gap in remaining
remaining = remaining.replace(gap, ' ' + components[0] +
    ' The full qualitative Bessel theorem, remaining replica integration, cyclic-to-interval transfer and inverse correlator existence remain missing.')
for field, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + field + r' = .*$', field + ' = ' + repr(value), source, flags=re.M)
counts = {'1124': '1128', '1110': '1113', '5248': '5255', '1128': '1131', '1119': '1122'}
source = re.sub(r'\b(?:1124|1110|5248|1128|1119)\b', lambda m: counts[m.group()], source)
source = source.replace('== 12', '== 7').replace("'theorem_count': 12", "'theorem_count': 7")
source = source.replace('new_theorems=12', 'new_theorems=7')
source = source.replace('new_axiom_reports=12', 'new_axiom_reports=7')
source = source.replace('new_module_count=4', 'new_module_count=3')
source = source.replace('new_theorem_count=12', 'new_theorem_count=7')
source = source.replace('new_selected_report_count=12', 'new_selected_report_count=7')
review = [
    'PROGRESS. This increment starts from the saved nested-correlation manifest. All retained proof-source hashes and selected axiom sets are checked unchanged; only root imports and the selected kernel registry are updated. The previous round helper, rerun after adding the three unregistered modules, rejects its old exact module count as expected; that observation is not counted as a successful new audit.',
    'A genuine nested generator supplies unit outer and inner inputs with the two required factor memberships. The existing scalar correlation-limit theorem is applied with the exact distinguished-input identity and both displayed lower containments. Uniqueness of the weighted Haar inner-product limit gives inner product zero against every actual unit test with vanishing next-order sum Gowers value.',
    'To infer target membership without assuming density of unit null tests, normalize the actual generator to (f+1)/2 in the unit interval. Its exact target projection has an actual unit-interval representative. The residual is unit bounded and orthogonal to the target, so the audited orthogonality equivalence gives vanishing target Gowers value. The new null-correlation lemma annihilates f against the residual, while constant one and the projected model annihilate it by target membership. Hence the residual has zero squared norm; undoing the affine normalization proves membership of f.',
    'The nested density equality identifies the complete intersection with the closed span of these genuine generators. Linear-span membership and closedness of the target extend the conclusion to every completed-space vector. The local step retains exactly the two positive lower-degree containments and a positive target degree.',
    'Strong induction uses total degree a+b for factor orders a+1 and b+1. The base a+b=0 is the previously audited first-order equality. In the first lower branch a>0, (a-1)+b is strictly smaller; in the second b>0, a+(b-1) is strictly smaller. Both containments use the same fixed subgroup sum, with the intersection membership reordered in the second branch. Natural-number degree identities are proved before applying the hypotheses. The final positive-degree theorem has no lower-containment hypothesis.',
    'Projection preservation places P_Q(P_R z) in both original factors. Full concatenation places it in the sum factor. Self-adjointness and orthogonality of z to that sum factor prove that P_Q z and P_R z are orthogonal. This holds for every vector in the completed Hilbert space, not just actual representatives.',
    'For actual representatives of the two projections, vanishing positive-order sum Gowers value gives orthogonality of the input by the audited implication. The completed-space projection result and weighted inner-product convergence then give null actual correlation. No pointwise bound on the represented input is added to this implication.',
    'One development rewrite expanded both arguments of an inner product and prevented the intended simplification. It was repaired by an explicit congruence in the first argument. No heartbeat or other set_option was introduced. All three focused compilations and the subsequent terminal full build and kernel reports are the accepted verification evidence.',
    'Seven theorems in three modules are audited. Full higher-order concatenation and its pair-projection orthogonality consequence are proved in the varying finite-subgroup, original weighted Haar specialization of the cited route. The full qualitative Bessel theorem, inverse correlator existence, the remaining integrations and the original StrongConjecture are still unproved. No complete formalization or prize eligibility is asserted.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://arxiv.org/html/1603.07815v4', reference_scope='Section 7 concatenation induction; subgroup uniformity variant and pair-projection consequence')\n"
) + source[end:]
Path('round-full-concatenation-audit.py').write_text(source, encoding='utf-8')
print('Prepared three-module audit: seven theorems.')
