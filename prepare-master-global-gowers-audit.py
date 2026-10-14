from pathlib import Path
import re

p = Path('round-master-short-geometry-audit.py')
s = p.read_text(encoding='utf-8')
s = s.replace("PREFIX = 'round-master-short-geometry'", "PREFIX = 'round-master-global-gowers'")
s = s.replace("OLD = 'round-full-window-short-gowers'", "OLD = 'round-master-short-geometry'")
s = s.replace('MasterPredictionShortCubeGeometry.lean', 'MasterOriginalShortCubeGowers.lean')
numbers = {'1061': '1062', '1062': '1063', '1044': '1045', '1053': '1054', '4945': '4946'}
s = re.sub(r'\b(?:1061|1062|1044|1053|4945)\b', lambda m: numbers[m[0]], s)
s = s.replace('== 3', '== 1').replace("'theorem_count': 3", "'theorem_count': 1")
s = s.replace('new_theorems=3', 'new_theorems=1').replace('new_axiom_reports=3', 'new_axiom_reports=1')
s = s.replace('new_theorem_count=3', 'new_theorem_count=1').replace('new_selected_report_count=3', 'new_selected_report_count=1')
components = ['The original harmonic full-window short-cube average is bounded by the actual retained-cell weighted subgroup Gowers value times (2J)^d, plus 4d/J and any positive epsilon, eventually uniformly over all admissible same-pool nonzero tested-polynomial evaluations and all real unit-bounded tests.']
remaining = 'The original same-pool master full-window short-cube Gowers specialization is proved. Comparison with signed-modulus and replica formulations, integration of rough-coprimality estimates, the deep Bessel input, cyclic-to-interval transfer and inverse correlator existence remain. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
review = ['PROGRESS. Baseline proof hashes are preserved.', 'The theorem instantiates actual prediction modulus P, quotient factors P/M and R/P, original interval width R, and original harmonic integerMass.', 'Positive quotient factors and nonempty short direction sets are derived from the original master conditions. Existential positivity witnesses are proved conclusions, not new assumptions.', 'The retained-cell index contains exactly aligned cells with admissible residues. Its weights are their actual harmonic masses divided by actual retained mass.', 'The finite full-window bound and the vanishing original remainder give a single eventual threshold uniform in same-pool x and all unit-bounded real tests.', 'The actual integer shift is P times the signed short difference sum. P is the positive absolute prediction modulus; equivalence with a signed-modulus formulation is not claimed here.', 'One new theorem is individually kernel audited. This theorem supplies a quantitative Gowers bound, not the missing Bessel or inverse theorem and not StrongConjecture.']
s = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), s, flags=re.M)
s = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), s, flags=re.M)
s = re.sub(r'        application_review=\[.*?\], new_modules=', '        application_review=' + repr(review) + ', new_modules=', s)
Path('round-master-global-gowers-audit.py').write_text(s, encoding='utf-8')
