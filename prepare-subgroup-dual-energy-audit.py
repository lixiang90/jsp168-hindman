from pathlib import Path
import re

s = Path('round-subgroup-bessel-energy-audit.py').read_text(encoding='utf-8')
s = s.replace("PREFIX = 'round-subgroup-bessel-energy'", "PREFIX = 'round-subgroup-dual-energy'")
s = s.replace("OLD = 'round-subgroup-haar-composition'", "OLD = 'round-subgroup-bessel-energy'")
s = s.replace('SubgroupBesselEnergy.lean', 'SubgroupDualEnergy.lean')
numbers = {'1068': '1069', '1069': '1070', '1051': '1052', '1060': '1061', '4969': '4976'}
s = re.sub(r'\b(?:1068|1069|1051|1060|4969)\b', lambda m: numbers[m[0]], s)
s = s.replace('len(set(names)) == 6', 'len(set(names)) == 7').replace('len(names) == 6', 'len(names) == 7')
s = s.replace('new_definitions=0', 'new_definitions=1').replace('new_axiom_reports=6', 'new_axiom_reports=7').replace('new_selected_report_count=6', 'new_selected_report_count=7')
components = ['The actual subgroup dual function is defined by averaging the nonroot cube product. It is unit-bounded for unit-bounded inputs, pairs with the original function to give the exact cube average, and equals the actual Haar average in dimension one. Arbitrary-order single-cell and weighted-cell Bessel energy reductions bound squared mean cube energies by the actual pairwise dual correlations.']
remaining = 'The signed original master short-cube and actual subgroup-combination estimates share the common probability system. First-order Bessel is proved. Arbitrary-order actual dual functions and their weighted energy reduction are now proved; controlling those dual correlations requires the still-missing higher-order concatenation and qualitative Bessel argument. Remaining replica integration, cyclic-to-interval transfer and inverse correlator existence are unfinished. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
review = ['PROGRESS. The previous audit was rechecked before saving the baseline; retained proof hashes unchanged.', 'The new definition is the actual finite average of the cube product with the root vertex erased. It is not a supplied dual-function certificate or an abstract surrogate.', 'The exact correlation identity reconstructs the original full cube product by reinserting the root. The unit bound uses the remaining unit-bounded factors.', 'Dimension one is proved equal to the previously verified subgroupHaarMean, checking consistency with the first-order Bessel result.', 'The arbitrary-order energy reduction uses the actual cube correlation, finite square expansion and Cauchy-Schwarz. The cell version uses nonnegative normalized original cell weights without changing coefficients.', 'The right-hand side remains an actual pairwise dual-function inner product. No unproved higher-order subgroup-sum bound or characteristic-factor commutation is inserted.', 'Six theorems and one definition are individually kernel audited. This is a genuine energy reduction, not a proof of the missing general Tao-Ziegler Bessel theorem.']
s = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), s, flags=re.M)
s = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), s, flags=re.M)
s = re.sub(r'        application_review=\[.*?\], new_modules=', '        application_review=' + repr(review) + ', new_modules=', s)
Path('round-subgroup-dual-energy-audit.py').write_text(s, encoding='utf-8')
