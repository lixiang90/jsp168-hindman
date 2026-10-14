from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('threshold', 'round-uniform-gowers-threshold-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-uniform-gowers-threshold-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-uniform-gowers-threshold'", "PREFIX = 'round-pair-gowers-testing'")
source = source.replace("OLD = 'round-recursive-localization'", "OLD = 'round-uniform-gowers-threshold'")
modules = ['Hindman168/SubgroupCubePairDerivative.lean', 'Hindman168/SubgroupGowersPairTesting.lean']
components = [
    'The original cube average is invariant under ambient translation. Averaging a pair-shift multiplicative derivative gives exactly the next cube order, and the corresponding Gowers moment identity preserves the original cell weights. A finite Haar testing estimate bounds mean absolute correlation by epsilon plus the next-order weighted Gowers power divided by a positive threshold power. Under an explicit eventual uniform small-test hypothesis, vanishing next-order Gowers values imply vanishing mean absolute correlation for varying finite subgroup systems along any filter.'
]
remaining = previous.REMAINING.replace(' Higher-order concatenation controlling dual correlations', ' ' + components[0] + ' Higher-order concatenation controlling dual correlations')
source = re.sub(r'^MODULES = .*$', 'MODULES = ' + repr(modules), source, flags=re.M)
source = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), source, flags=re.M)
source = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), source, flags=re.M)
counts = {'1106': '1108', '1090': '1092', '5156': '5163', '1108': '1110', '1099': '1101'}
source = re.sub(r'\b(?:1106|1090|5156|1108|1099)\b', lambda m: counts[m.group()], source)
for old_text, new_text in [
    ('== 4', '== 7'), ("'theorem_count': 4", "'theorem_count': 7"),
    ('new_theorems=4', 'new_theorems=7'), ('new_axiom_reports=4', 'new_axiom_reports=7'),
    ('new_theorem_count=4', 'new_theorem_count=7'), ('new_selected_report_count=4', 'new_selected_report_count=7')
]:
    source = source.replace(old_text, new_text)
review = [
    'PROGRESS. The uniform-Gowers-threshold round was rechecked before edits. Retained proof source hashes and axiom sets remain unchanged.',
    'Ambient translation invariance is proved for the actual real cube product and normalized cube average. A pair of subgroup shifts is reduced to their difference, and exact Haar translation invariance gives the next-order derivative identity.',
    'The weighted Gowers identity uses the actual positive-degree power identity, interchanges only finite sums and finite Haar means, and retains each original nonnegative cell weight. No replacement of the weighted norm by separate unweighted cell norms occurs.',
    'The small-test estimate separates tests with size at most the positive threshold from the remaining tests. On the latter, the size power divided by the threshold power is at least one. This proves a pointwise majorant and its averaged bound without assuming that the size is bounded or that the parameter type has bounded cardinality.',
    'Applying the estimate twice to the subgroup shift parameters and then the exact derivative moment gives epsilon plus the next-order Gowers power divided by the fixed threshold power. The correlation bound of one and the eventual small-test hypothesis are explicit premises.',
    'For varying finite systems, the threshold is chosen after epsilon and then fixed while the next-order moment tends to zero. The resulting mean absolute correlation tends to zero along the same filter. The convergence theorem applies to any filter; it does not silently use a countable intersection or discard the original weights.',
    'Seven theorems are audited. This closes the numerical averaging and Markov step needed by future concatenation. It does not prove localized-generator density, the higher-order containment supplying structured coefficients, the full Bessel theorem, or the original main target.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING)\n'
) + source[end:]
Path('round-pair-gowers-testing-audit.py').write_text(source, encoding='utf-8')
print('Prepared two-module, seven-theorem audit against the current saved baseline.')
