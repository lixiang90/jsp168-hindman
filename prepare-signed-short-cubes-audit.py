from pathlib import Path
import re

s = Path('round-master-cell-probability-audit.py').read_text(encoding='utf-8')
s = s.replace("PREFIX = 'round-master-cell-probability'", "PREFIX = 'round-signed-short-cubes'")
s = s.replace("OLD = 'round-master-common-cyclic'", "OLD = 'round-master-cell-probability'")
s = s.replace('MasterCommonCellProbability.lean', 'SignedShortCubeSymmetry.lean')
numbers = {'1065': '1066', '1066': '1067', '1048': '1049', '1057': '1058', '4954': '4957'}
s = re.sub(r'\b(?:1065|1066|1048|1057|4954)\b', lambda m: numbers[m[0]], s)
s = s.replace('== 2', '== 3').replace("'theorem_count': 2", "'theorem_count': 3")
s = s.replace('new_theorems=2', 'new_theorems=3').replace('new_axiom_reports=2', 'new_axiom_reports=3')
s = s.replace('new_theorem_count=2', 'new_theorem_count=3').replace('new_selected_report_count=2', 'new_selected_report_count=3')
components = ['Short-cube double averages are exactly invariant under negating their integer modulus and hence equal the averages with its natural absolute value. The original signed prediction modulus now satisfies the common-cyclic full-window Gowers bound with unchanged harmonic weights and error.']
remaining = 'The signed original master short-cube estimate and actual conditioned subgroup-combination estimate now share the common cyclic group R/M and normalized harmonic cell weights. The deep Bessel theorem remains missing, as do remaining replica integration, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
review = ['PROGRESS. Prior audit rechecked and baseline proof hashes preserved.', 'Exchanging the two independent uniform short-vector variables negates every increment simultaneously. The proof establishes equality of full cube averages for arbitrary vertex-specific real functions.', 'The symmetry is valid also for zero dimension, zero interval length and zero modulus. It does not silently assume a nonempty averaging set or boundedness.', 'The absolute-value identity follows by splitting the sign of the integer modulus. Applying it root by root leaves the original harmonic root law exactly unchanged.', 'The new common-cyclic master theorem uses the actual signed predictionCubeModulus in integer shifts, while subgroup generator and short interval length retain its natural absolute value.', 'Three new theorems are individually audited. This resolves the signed-modulus interface without adding an error term or changing the subgroup. Bessel, inverse and final extraction gaps remain.']
s = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), s, flags=re.M)
s = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), s, flags=re.M)
s = re.sub(r'        application_review=\[.*?\], new_modules=', '        application_review=' + repr(review) + ', new_modules=', s)
Path('round-signed-short-cubes-audit.py').write_text(s, encoding='utf-8')
