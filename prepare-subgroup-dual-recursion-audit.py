from pathlib import Path
import re

s = Path('round-subgroup-dual-energy-audit.py').read_text(encoding='utf-8')
s = s.replace("PREFIX = 'round-subgroup-dual-energy'", "PREFIX = 'round-subgroup-dual-recursion'")
s = s.replace("OLD = 'round-subgroup-bessel-energy'", "OLD = 'round-subgroup-dual-energy'")
s = s.replace('SubgroupDualEnergy.lean', 'SubgroupDualRecursion.lean')
numbers = {'1069': '1070', '1070': '1071', '1052': '1053', '1061': '1062', '4976': '4982'}
s = re.sub(r'\b(?:1069|1070|1052|1061|4976)\b', lambda m: numbers[m[0]], s)
s = s.replace('len(set(names)) == 7', 'len(set(names)) == 6').replace('len(names) == 7', 'len(names) == 6')
s = s.replace('new_definitions=1', 'new_definitions=0').replace('new_axiom_reports=7', 'new_axiom_reports=6').replace('new_selected_report_count=7', 'new_selected_report_count=6')
components = ['Actual nonroot cube products are split by a new coordinate, with exact image reindexing. This proves the subgroup dual-function recursion D_(d+1) f(x) = mean_a f(x+a) D_d(f times translated f)(x), as well as its zero-order base case and translation covariance.']
remaining = 'The signed master short-cube and actual subgroup-combination estimates share the common probability system. First-order Bessel is proved. Arbitrary-order actual dual functions, weighted energy reduction and exact dimension recursion are proved. Higher-order concatenation controlling dual correlations and the full qualitative Bessel theorem remain missing, as do remaining replica integration, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
review = ['PROGRESS. Previous audit rechecked and all baseline proof hashes retained.', 'The combinatorial splitting partitions the nonempty subsets according to whether the new coordinate is present. Injectivity and disjointness are proved explicitly.', 'Reindexing under an injective coordinate map preserves the erased empty vertex and all remaining products.', 'The actual nonroot cube derivative identity is proved without cancelling or dividing by f(x), so zero values of the root cause no exception.', 'The dual recursion uses the exact normalized finite means and the original multiplicative difference. The zero-order value and translation covariance are separately proved.', 'Six new theorems are individually audited, with no new definitions or hypotheses asserting a high-order structure theorem. These are tools for the missing concatenation induction, not its conclusion.']
s = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), s, flags=re.M)
s = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), s, flags=re.M)
s = re.sub(r'        application_review=\[.*?\], new_modules=', '        application_review=' + repr(review) + ', new_modules=', s)
Path('round-subgroup-dual-recursion-audit.py').write_text(s, encoding='utf-8')
