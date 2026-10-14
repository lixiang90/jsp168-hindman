from pathlib import Path
import re

s = Path('round-signed-short-cubes-audit.py').read_text(encoding='utf-8')
s = s.replace("PREFIX = 'round-signed-short-cubes'", "PREFIX = 'round-subgroup-haar-composition'")
s = s.replace("OLD = 'round-master-cell-probability'", "OLD = 'round-signed-short-cubes'")
s = s.replace('SignedShortCubeSymmetry.lean', 'SubgroupHaarComposition.lean')
numbers = {'1066': '1067', '1067': '1068', '1049': '1050', '1058': '1059', '4957': '4963'}
s = re.sub(r'\b(?:1066|1067|1049|1058|4957)\b', lambda m: numbers[m[0]], s)
s = s.replace('== 3', '== 6').replace("'theorem_count': 3", "'theorem_count': 6")
s = s.replace('new_theorems=3', 'new_theorems=6').replace('new_axiom_reports=3', 'new_axiom_reports=6')
s = s.replace('new_theorem_count=3', 'new_theorem_count=6').replace('new_selected_report_count=3', 'new_selected_report_count=6')
components = ['Finite Haar averages push forward exactly under surjective additive homomorphisms. Actual subgroup averaging operators compose to averaging over the subgroup sum, commute, are idempotent and self-adjoint. The inner product of two subgroup averages equals the original one-dimensional cube energy for their subgroup sum.']
remaining = 'The signed original master short-cube and actual subgroup-combination estimates share the common probability system. Actual subgroup Haar composition and pair-energy identities now supply the first-order operator foundation for Bessel. Higher-order characteristic-factor concatenation and the full qualitative Bessel theorem remain missing, as do remaining replica integration, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
review = ['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.', 'Consulted Tao and Ziegler, arXiv:1603.07815v4, Theorem 1.23 and Section 8, https://arxiv.org/html/1603.07815v4#S8. The qualitative Bessel proof uses fixed-family reduction, characteristic-factor concatenation, and an energy argument; it is not a consequence of coprimality alone.', 'Generic intersection information for subspaces is not treated as proof that their projections commute or are orthogonal. This round establishes the relevant identities directly for actual finite subgroup Haar averages in first order.', 'The homomorphism pushforward identity follows from translation invariance and interchange of finite means. The map Q times R to Q supremum R is the actual sum map and is proved surjective.', 'Composition, commutation, idempotence and self-adjointness are exact identities for arbitrary real functions. The pair-energy identity refers to the previously defined actual one-dimensional subgroupCubeAverage.', 'Six new theorems are individually kernel audited, with no new definitions, axioms or assumed projection identities. No higher-order Bessel conclusion is claimed.']
s = re.sub(r'^COMPONENTS = .*$', 'COMPONENTS = ' + repr(components), s, flags=re.M)
s = re.sub(r'^REMAINING = .*$', 'REMAINING = ' + repr(remaining), s, flags=re.M)
s = re.sub(r'        application_review=\[.*?\], new_modules=', '        application_review=' + repr(review) + ', new_modules=', s)
Path('round-subgroup-haar-composition-audit.py').write_text(s, encoding='utf-8')
