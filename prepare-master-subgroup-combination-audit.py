from pathlib import Path
import re

s = Path('round-master-global-gowers-audit.py').read_text(encoding='utf-8')
s = s.replace("PREFIX = 'round-master-global-gowers'", "PREFIX = 'round-master-subgroup-combination'")
s = s.replace("OLD = 'round-master-short-geometry'", "OLD = 'round-master-global-gowers'")
s = s.replace('MasterOriginalShortCubeGowers.lean', 'MasterSubgroupCombination.lean')
numbers = {'1062': '1063', '1063': '1064', '1045': '1046', '1054': '1055', '4946': '4949'}
s = re.sub(r'\b(?:1062|1063|1045|1054|4946)\b', lambda m: numbers[m[0]], s)
s = s.replace('len(set(names)) == 1', 'len(set(names)) == 3').replace('len(names) == 1', 'len(names) == 3')
s = s.replace("for kind, _ in values) == 1", "for kind, _ in values) == 3")
s = s.replace("'theorem_count': 1", "'theorem_count': 3").replace('new_theorems=1', 'new_theorems=3')
s = s.replace('new_axiom_reports=1', 'new_axiom_reports=3').replace('new_theorem_count=1', 'new_theorem_count=3').replace('new_selected_report_count=1', 'new_selected_report_count=3')
components = ['The actual prediction-modulus quotient equals the rough polynomial value. Under actual separately conditioned master prime-pool laws, the mean of the Gowers norm for sums of these generated subgroups is eventually at most the full-group norm plus any positive epsilon, uniformly in positive cyclic size, positive base modulus, finite cell probability system, positive dimension and unit-bounded real tests.']
remaining = 'The original master short-cube bound and conditioned rough-coprimality-to-subgroup-sum Gowers estimate are proved. Their common cyclic-model identification and replica/signed-modulus comparison remain, together with the deep Bessel theorem, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
review = ['PROGRESS. The previous round was rechecked before saving this baseline.', 'The natural prediction-modulus quotient is proved equal to the actual rough polynomial value using a positive base modulus, including zero evaluations.', 'A finite-mass good-event bound retains the original coefficients and charges the actual complementary event mass. It assumes only a normalized nonnegative finite law and a statistic bounded above by one.', 'The master specialization uses actual conditionMass on primeSampleGood, not replacement uniform tuple weights. Its normalization follows from the already proved event-mass limit.', 'On the nonzero rough-coprime event, Bezout gives the full cyclic group as subgroup sum. On the complement the unit bound controls the loss. This proves the exact combining-subgroups estimate in the paper.', 'The eventual threshold is uniform in all subsequently quantified cell types and probabilities, positive moduli and dimensions, and bounded real tests. No Bessel or inverse theorem is assumed.', 'This does not yet identify the cyclic groups and cells with the previous short-cube theorem or prove the Bessel step. The full target remains unproved.']
s = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), s, flags=re.M)
s = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), s, flags=re.M)
s = re.sub(r'        application_review=\[.*?\], new_modules=', '        application_review=' + repr(review) + ', new_modules=', s)
Path('round-master-subgroup-combination-audit.py').write_text(s, encoding='utf-8')
