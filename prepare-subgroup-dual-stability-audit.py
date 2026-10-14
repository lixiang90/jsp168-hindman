from pathlib import Path
import re

s = Path('round-subgroup-dual-recursion-audit.py').read_text(encoding='utf-8')
s = s.replace("PREFIX = 'round-subgroup-dual-recursion'", "PREFIX = 'round-subgroup-dual-stability'")
s = s.replace("OLD = 'round-subgroup-dual-energy'", "OLD = 'round-subgroup-dual-recursion'")
s = s.replace('SubgroupDualRecursion.lean', 'SubgroupDualStability.lean')
numbers = {'1070': '1071', '1071': '1072', '1053': '1054', '1062': '1063', '4982': '4988'}
s = re.sub(r'\b(?:1070|1071|1053|1062|4982)\b', lambda m: numbers[m[0]], s)
components = ['Actual subgroup dual functions obey an L1 perturbation bound with factor 2^d-1, independent of group and subgroup sizes. Their mean squared difference is at most twice this factor times the original input L1 difference. The proof retains original finite Haar laws through a nonroot product telescoping bound and exact translation invariance.']
remaining = 'The signed master short-cube and subgroup-combination estimates share the actual probability system. First-order Bessel, arbitrary-order dual energy reduction, recursion and uniform L1-to-L2 stability are proved. Higher-order concatenation controlling dual correlations and the full qualitative Bessel theorem remain missing, as do remaining replica integration, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
review = ['PROGRESS. Prior audit rechecked and all retained proof hashes unchanged.', 'The product perturbation bound is proved by finite-set induction for two unit-bounded real factor families. It sums actual factor differences and does not divide by potentially zero factors.', 'The pointwise dual bound keeps the original short cube-direction Haar average and exact nonroot vertex sum.', 'Interchanging root and direction averages and translating the root identifies every vertex error with the original input L1 error. The exact number of nonroot vertices gives the factor 2^d-1, including dimension zero.', 'The squared-error bound uses the proved unit bounds on both actual dual functions, giving output L2 squared at most 2*(2^d-1) times input L1. Constants are uniform in all finite groups and subgroups.', 'Six new theorems are individually audited. These justify perturbation in prospective approximation arguments; no higher-order concatenation or Bessel conclusion is assumed or claimed.']
s = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), s, flags=re.M)
s = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), s, flags=re.M)
s = re.sub(r'        application_review=\[.*?\], new_modules=', '        application_review=' + repr(review) + ', new_modules=', s)
Path('round-subgroup-dual-stability-audit.py').write_text(s, encoding='utf-8')
