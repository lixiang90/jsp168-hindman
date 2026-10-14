from pathlib import Path
import re

s = Path('round-subgroup-haar-composition-audit.py').read_text(encoding='utf-8')
s = s.replace("PREFIX = 'round-subgroup-haar-composition'", "PREFIX = 'round-subgroup-bessel-energy'")
s = s.replace("OLD = 'round-signed-short-cubes'", "OLD = 'round-subgroup-haar-composition'")
s = s.replace('SubgroupHaarComposition.lean', 'SubgroupBesselEnergy.lean')
numbers = {'1067': '1068', '1068': '1069', '1050': '1051', '1059': '1060', '4963': '4969'}
s = re.sub(r'\b(?:1067|1068|1050|1059|4963)\b', lambda m: numbers[m[0]], s)
components = ['A first-order Bessel energy bound is proved for actual finite subgroup averages, then for the original weighted cell system. For any probability weights on subgroups and cells, the fourth power of the mean weighted first-order Gowers value is at most the pairwise mean first-order Gowers value of subgroup sums.']
remaining = 'The signed original master short-cube and actual subgroup-combination estimates share the common probability system. First-order Bessel now has an explicit fourth-power bound for arbitrary finite subgroup and cell probability weights. The required arbitrary higher-order characteristic-factor concatenation and qualitative Bessel theorem remain missing, as do remaining replica integration, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
review = ['PROGRESS. Prior audit rechecked before saving the baseline; old proof hashes preserved.', 'The weighted square identity expands the actual sum of subgroup Haar averages and applies the previously proved pair-energy identity term by term.', 'Cauchy-Schwarz with the unit-bounded original function proves the first-order energy inequality. This part even allows signed subgroup coefficients.', 'An elementary variance proof gives Jensen for weighted squares. Applying it to actual nonnegative normalized cell weights produces the weighted-cell energy inequality.', 'For normalized nonnegative subgroup weights, the square-root identity for actual first-order Gowers values and their unit bounds yield the quartic Bessel inequality. No projection or orthogonality assumption is introduced.', 'Six new theorems are individually kernel audited. The quartic result is first-order only; it is not a substitute for the arbitrary-order Tao-Ziegler theorem required by the master short-cube argument.']
s = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), s, flags=re.M)
s = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), s, flags=re.M)
s = re.sub(r'        application_review=\[.*?\], new_modules=', '        application_review=' + repr(review) + ', new_modules=', s)
Path('round-subgroup-bessel-energy-audit.py').write_text(s, encoding='utf-8')
