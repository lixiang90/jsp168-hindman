from pathlib import Path
import re

s = Path('round-haar-sampling-variance-audit.py').read_text(encoding='utf-8')
s = s.replace("PREFIX = 'round-haar-sampling-variance'", "PREFIX = 'round-weighted-dual-approximation'")
s = s.replace("OLD = 'round-subgroup-dual-stability'", "OLD = 'round-haar-sampling-variance'")
s = s.replace('HaarSamplingVariance.lean', 'WeightedDualApproximation.lean')
numbers = {'1072': '1073', '1073': '1074', '1055': '1056', '1064': '1065', '4994': '4998'}
s = re.sub(r'\b(?:1072|1073|1055|1064|4994)\b', lambda m: numbers[m[0]], s)
s = s.replace('== 6', '== 4').replace("'theorem_count': 6", "'theorem_count': 4")
s = s.replace('new_theorems=6', 'new_theorems=4').replace('new_axiom_reports=6', 'new_axiom_reports=4')
s = s.replace('new_theorem_count=6', 'new_theorem_count=4').replace('new_selected_report_count=6', 'new_selected_report_count=4')
components = ['For arbitrary nonnegative normalized cell probabilities, one common set of m subgroup-direction samples approximates the actual dual function in weighted squared L2 error at most 1/m. The empirical function remains unit-bounded, and the same samples give squared correlation error at most 1/m simultaneously for every unit-bounded test on all cells.']
remaining = 'The common-system master estimates, first-order Bessel, dual energy reduction, recursion and stability are proved. Actual dual functions now have a common finite empirical approximation preserving arbitrary cell probabilities, unit bounds and uniform bounded-test correlations. Higher-order concatenation controlling dual correlations and the full qualitative Bessel theorem remain missing, as do remaining replica integration, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
review = ['PROGRESS. Previous round rechecked and all retained proof hashes preserved.', 'The weighted sampling result retains the supplied actual nonnegative normalized cell probabilities. It selects one sample tuple for the aggregate error, rather than separately changing the law in each cell.', 'Weighted Cauchy-Schwarz is proved from the existing weighted square inequality and root Haar Cauchy-Schwarz, with all coefficients retained.', 'The dual approximation is an empirical mean of actual nonroot cube products. Its unit bound follows from the unit bounds of those products and m>0.', 'The existential sample tuple precedes universal quantification over bounded tests. Thus all such tests share the same approximation and squared correlation error bound 1/m.', 'Four new theorems are individually audited. Neither a high-order concatenation assertion nor a substitute probability system is introduced; the principal Bessel and inverse gaps remain.']
s = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), s, flags=re.M)
s = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), s, flags=re.M)
s = re.sub(r'        application_review=\[.*?\], new_modules=', '        application_review=' + repr(review) + ', new_modules=', s)
Path('round-weighted-dual-approximation-audit.py').write_text(s, encoding='utf-8')
