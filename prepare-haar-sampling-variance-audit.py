from pathlib import Path
import re

s = Path('round-subgroup-dual-stability-audit.py').read_text(encoding='utf-8')
s = s.replace("PREFIX = 'round-subgroup-dual-stability'", "PREFIX = 'round-haar-sampling-variance'")
s = s.replace("OLD = 'round-subgroup-dual-recursion'", "OLD = 'round-subgroup-dual-stability'")
s = s.replace('SubgroupDualStability.lean', 'HaarSamplingVariance.lean')
numbers = {'1071': '1072', '1072': '1073', '1054': '1055', '1063': '1064', '4988': '4994'}
s = re.sub(r'\b(?:1071|1072|1054|1063|4988)\b', lambda m: numbers[m[0]], s)
components = ['Exact finite independent sampling variance is proved. Every unit-bounded finite kernel has an empirical m-sample approximation with mean squared error at most 1/m. In particular, each actual subgroup dual function admits such an approximation by m actual nonroot cube products, uniformly in group and subgroup sizes.']
remaining = 'The common-system master estimates, first-order Bessel, arbitrary-order dual energy reduction, recursion and stability are proved. Actual dual functions now have dimension-uniform finite empirical L2 approximation. Higher-order concatenation controlling dual correlations and the full qualitative Bessel theorem remain missing, as do remaining replica integration, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
review = ['PROGRESS. Previous audit rechecked and baseline proof hashes preserved.', 'Centered sample means and second moments are proved by induction on the number of actual independent finite coordinates. No independence certificate is assumed.', 'The sample variance identity keeps the exact 1/m normalization and requires m>0 explicitly.', 'For a unit-bounded finite kernel, exchanging sample and root averages bounds the expected squared error by 1/m. An actual sample no worse than the finite mean is then selected.', 'The dual-function instance uses the original nonroot cube products and original subgroup Haar directions. Its squared L2 error is at most 1/m, independent of group size and cube dimension.', 'Six new theorems are individually audited, without increased heartbeat limits or assumed approximation results. This finite approximation is not itself the higher-order concatenation theorem.']
s = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), s, flags=re.M)
s = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), s, flags=re.M)
s = re.sub(r'        application_review=\[.*?\], new_modules=', '        application_review=' + repr(review) + ', new_modules=', s)
Path('round-haar-sampling-variance-audit.py').write_text(s, encoding='utf-8')
