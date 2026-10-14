from pathlib import Path
import re

s = Path('round-master-common-cyclic-audit.py').read_text(encoding='utf-8')
s = s.replace("PREFIX = 'round-master-common-cyclic'", "PREFIX = 'round-master-cell-probability'")
s = s.replace("OLD = 'round-master-subgroup-combination'", "OLD = 'round-master-common-cyclic'")
s = s.replace('MasterCommonCyclicShortCube.lean', 'MasterCommonCellProbability.lean')
numbers = {'1064': '1065', '1065': '1066', '1047': '1048', '1056': '1057', '4952': '4954'}
s = re.sub(r'\b(?:1064|1065|1047|1056|4952)\b', lambda m: numbers[m[0]], s)
s = s.replace('== 3', '== 2').replace("'theorem_count': 3", "'theorem_count': 2")
s = s.replace('new_theorems=3', 'new_theorems=2').replace('new_axiom_reports=3', 'new_axiom_reports=2')
s = s.replace('new_theorem_count=3', 'new_theorem_count=2').replace('new_selected_report_count=3', 'new_selected_report_count=2')
components = ['The actual aligned master-cell harmonic weights are eventually nonnegative and normalized. The rough-coprimality subgroup-sum Gowers bound is instantiated on those exact weights, the common cyclic group R/M, the original affine cell tests and the actual separately conditioned prime-tuple law.']
remaining = 'The original master short-cube and subgroup-combination estimates now share the common cyclic group R/M and actual normalized harmonic cell weights. The deep Bessel theorem is still missing, as are replica/signed-modulus comparison, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
review = ['PROGRESS. The prior audit was rechecked and all baseline proof hashes preserved.', 'Cell positivity and normalization are proved for the original retained harmonic mass, using its eventual strict positivity, primorial divisibility and the exact aligned partition.', 'The common interval width is M*(R/M)=R, derived from the actual master divisibility. Finite product and subtype sums retain every original admissible cell coefficient.', 'The subgroup-combination theorem is specialized to the actual constructed master family. Its required master conditions are constructed with the empty rational coefficient set; no new master-condition hypothesis is introduced.', 'The cyclic group, original affine cell tests, cell probabilities and separately conditioned prime-tuple law agree with the common-model short-cube setup. The quantitative loss remains epsilon, uniformly over positive dimensions and all unit-bounded integer tests.', 'Two new theorems are individually audited. The result does not supply the Bessel implication from subgroup-sum norms to individual subgroup norms. Deep inverse and final extraction steps remain.']
s = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), s, flags=re.M)
s = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), s, flags=re.M)
s = re.sub(r'        application_review=\[.*?\], new_modules=', '        application_review=' + repr(review) + ', new_modules=', s)
Path('round-master-cell-probability-audit.py').write_text(s, encoding='utf-8')
