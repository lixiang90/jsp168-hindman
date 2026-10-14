from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-nested-recursion-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-nested-recursion-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-nested-recursion'", "PREFIX = 'round-nested-correlation'")
source = source.replace("OLD = 'round-nested-dual-density'", "OLD = 'round-nested-recursion'")
modules = ['Hindman168/WeightedHaarRecursiveCauchySchwarz.lean', 'Hindman168/SubgroupSumPairMoment.lean',
           'Hindman168/NestedMixedDualCorrelation.lean', 'Hindman168/NestedMixedDualCorrelationLimit.lean']
components = [
    'The original weighted correlation now has a verified recursive Cauchy-Schwarz duplication bound. Actual translated representations are averaged over shift and core parameters, preserving the original cell probabilities; only the core needs unit bounds for this estimate. Exact subgroup-sum Haar and paired-shift identities reduce independently sampled summand shifts to the Haar law on the subgroup sum. The corresponding genuine next-order Gowers moment and finite threshold bound are proved. The exact two-level dual expansion supplies the recursive representation, giving a finite correlation-square bound by epsilon plus the next-order subgroup-sum Gowers power divided by a positive threshold power. Under the two explicit lower intersection containments, the audited uniform paired-coefficient threshold supplies this finite bound eventually for every selected unit test. Thus vanishing next-order subgroup-sum Gowers values imply vanishing actual nested-dual correlation along the same tail-containing ultrafilter. No subgroup-cardinality bound or replacement of original cell weights is used.'
]
old_gap = ' The exact two-level expansion and uniform paired-coefficient testing still need to be connected through the weighted Cauchy-Schwarz estimate, subgroup-sum Haar averaging and next-order Gowers moment to the higher-order concatenation induction.'
assert old_gap in previous.REMAINING
remaining = previous.REMAINING.replace(old_gap,
    ' ' + components[0] + ' Null correlation for genuine nested generators still needs to be extended to membership in the next-order subgroup-sum closed dual space, and both lower containments discharged by the higher-order concatenation induction.')
source = re.sub(r'^MODULES = .*$', 'MODULES = ' + repr(modules), source, flags=re.M)
source = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), source, flags=re.M)
source = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), source, flags=re.M)
counts = {'1121': '1124', '1106': '1110', '5236': '5248', '1124': '1128', '1115': '1119'}
source = re.sub(r'\b(?:1121|1106|5236|1124|1115)\b', lambda m: counts[m.group()], source)
source = source.replace('assert len(names) == len(set(names)) == 10', 'assert len(names) == len(set(names)) == 12')
source = source.replace('for kind, _ in values) == 8', 'for kind, _ in values) == 12')
source = source.replace("'theorem_count': 8", "'theorem_count': 12")
source = source.replace('and len(names) == 10', 'and len(names) == 12')
for old_text, new_text in [
    ('new_theorems=8', 'new_theorems=12'), ('new_definitions=2', 'new_definitions=0'),
    ('new_axiom_reports=10', 'new_axiom_reports=12'), ('new_module_count=3', 'new_module_count=4'),
    ('new_theorem_count=8', 'new_theorem_count=12'), ('new_selected_report_count=10', 'new_selected_report_count=12')
]:
    source = source.replace(old_text, new_text)
review = [
    'PROGRESS. The nested-recursion round was rechecked before edits. Retained proof hashes, kernel axiom sets and pinned dependencies remain unchanged.',
    'Finite weighted Haar means commute with internal finite averaging by finite-sum and Haar linearity. The cell weights remain the original p(c); there is no unweighted replacement of the cell law. The average-square identity is proved by two independent finite Haar averages.',
    'Ambient translations, allowed to depend on the shift parameter and original cell, preserve the original weighted correlation exactly. For an actual translated recursive representation, the correlation is reorganized as an average of core-weighted shift averages. Cauchy-Schwarz first squares the core average and then discards the unit core in the original weighted law. The resulting squared shift average is expanded exactly into two copies and bounded by the absolute paired correlation.',
    'The generic recursive square estimate assumes normalized nonnegative original cell weights, nonempty finite shift/core parameter types and a pointwise exact representation. It needs unit bounds only on the core, not on either the recursive coefficients or the tested function. All of these premises are displayed in the statement.',
    'The sum-subgroup Haar identity specializes the audited surjective addition-homomorphism result. Independently averaging a pair of Q-by-R shifts gives exactly the paired Haar law on Q sup R. The genuine weighted next-order Gowers moment is then transferred to this sampling law, with no bound on fiber size or subgroup cardinality.',
    'The finite power-threshold estimate is applied to each sampled shift pair. Averaging and the verified sum-subgroup moment yield epsilon plus the next-order weighted Gowers power divided by the positive threshold power. The lower order is explicitly positive, and the threshold is strictly positive; no unsupported division or zero-order norm identity is used.',
    'For an actual nested dual, the shift parameters and core parameters are both Q times R. The actual two-level expansion discharges the generic representation premise. The core is the translated distinguished inner singleton input, so its unit bound follows from the nonroot inner input bound.',
    'The finite nested correlation bound supplies the trivial paired-test unit bound using the actual double-coefficient bounds, the unit test bound, normalized original cell weights and the finite Haar absolute bound. Its small-test condition is explicit. The Markov estimate is uniform in the core parameter, which permits averaging over the entire core law without a cardinality bound.',
    'The varying-stage limit theorem applies the audited uniform paired-coefficient threshold under both explicitly displayed lower intersection containments. For each sampled shift pair, its multiplicative test derivative is unit bounded. The two coefficient parameter choices are inserted into the Fin 2 product threshold, and their exact product is matched by finite-product evaluation and commutative ring identities.',
    'The threshold is selected for epsilon squared divided by two before using convergence of the next-order Gowers value. Its reciprocal power is therefore fixed along the limit. The remaining Gowers-power term tends to zero; the finite squared-correlation bound gives absolute correlation less than epsilon. This establishes genuine scalar null correlation on the same ultrafilter.',
    'A development elaboration timeout was repaired by explicitly supplying the Q-by-R shift and core parameter types. The default heartbeat bound was not raised. Failed development commands are not treated as evidence; only terminal successful focused compilations, full build and complete selected kernel reports are accepted.',
    'This follows Section 7 correlation duplication, threshold and moment steps, specialized to actual finite subgroup Haar laws. The positive lower intersection containments remain premises for the induction hypothesis. Closed-space membership of all nested generators, extension through the nested density equality and discharge of the induction remain work.',
    'Twelve theorems in four modules are audited. The actual nested correlation-limit step is now proved. Full higher-order concatenation, qualitative Bessel, inverse correlator existence and the original StrongConjecture remain unproved.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://arxiv.org/html/1603.07815v4', reference_scope='Section 7 correlation duplication, threshold and moment; subgroup uniformity variant')\n"
) + source[end:]
Path('round-nested-correlation-audit.py').write_text(source, encoding='utf-8')
print('Prepared four-module audit: twelve theorems.')
