from pathlib import Path
import re

s = Path('round-master-subgroup-combination-audit.py').read_text(encoding='utf-8')
s = s.replace("PREFIX = 'round-master-subgroup-combination'", "PREFIX = 'round-master-common-cyclic'")
s = s.replace("OLD = 'round-master-global-gowers'", "OLD = 'round-master-subgroup-combination'")
s = s.replace('MasterSubgroupCombination.lean', 'MasterCommonCyclicShortCube.lean')
numbers = {'1063': '1064', '1064': '1065', '1046': '1047', '1055': '1056', '4949': '4952'}
s = re.sub(r'\b(?:1063|1064|1046|1055|4949)\b', lambda m: numbers[m[0]], s)
components = ['The actual full-window short-cube bound is now on the common cyclic group ZMod(R/M), with group, cell index and original cell probabilities fixed before quantifying the sampled prime tuple. Exact order transport preserves the Gowers value and the full previous error bound.']
remaining = 'The original master short-cube bound now uses the common cyclic group R/M, and the actual conditioned subgroup-sum estimate is proved. Instantiation of both bounds with the same verified cell probability system and replica/signed-modulus comparison remain, together with the deep Bessel theorem, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
review = ['PROGRESS. The previous audit was rechecked and all baseline proof hashes preserved.', 'The cyclic-order transport lemma proves equality of the actual weighted subgroup Gowers values for equal natural orders, with identical integer-coordinate test values and weights. Dependent finite-type instances are transported by equality elimination.', 'Positivity of R/M holds at every master stage, derived from original positive gap and modulus divisibility, without selecting a tuple.', 'The new full-window theorem fixes ZMod(R/M), aligned cells and original harmonic cell weights before quantifying same-pool tuples. It therefore does not silently use a tuple-dependent ambient group.', 'The exact factorization R/M=(P/M)*(R/P) transports the previous theorem with no additional error or hypothesis. Original shift P, interval, weights, bounded tests and uniform threshold are preserved.', 'Three new theorems are individually audited. The Bessel input, inverse theorem and full target remain unproved; connecting the common cell probability normalization to the subgroup-combination theorem is still required.']
s = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), s, flags=re.M)
s = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), s, flags=re.M)
s = re.sub(r'        application_review=\[.*?\], new_modules=', '        application_review=' + repr(review) + ', new_modules=', s)
Path('round-master-common-cyclic-audit.py').write_text(s, encoding='utf-8')
