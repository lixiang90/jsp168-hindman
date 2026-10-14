from pathlib import Path
import re
source=Path('round-cube-fixing-directions-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-cube-fixing-directions'", "PREFIX = 'round-retained-root-cube'").replace("OLD = 'round-invariant-factor-cauchy'", "OLD = 'round-cube-fixing-directions'")
counts={'1002':'1004','1004':'1005','986':'987','995':'996','4791':'4797'}
source=re.sub(r'\b(?:1002|1004|986|995|4791)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=11','new_theorems=6').replace('new_theorem_count=11','new_theorem_count=6').replace('new_definitions=3','new_definitions=0').replace('new_module_count=2','new_module_count=1')
source=source.replace('== 11\n    root','== 6\n    root').replace("'theorem_count': 11","'theorem_count': 6")
source=source.replace('len(set(names)) == 14','len(set(names)) == 6').replace('len(names) == 14','len(names) == 6').replace('new_axiom_reports=14','new_axiom_reports=6').replace('new_selected_report_count=14','new_selected_report_count=6')
modules=['Hindman168/RetainedRootCube.lean']
components=[
 'For any finite family of additive directions on the original cube parameter group whose root response is the subgroup increment, the product of retained root copies equals the original subgroup cube product exactly. Averaging over all original parameters recovers the original subgroup cube mean.',
 'Each root-response direction is injective, so its image subgroup Haar mean is exactly reparameterized by the original subgroup. A dependent product of these equivalences proves the exact root-cube average identity for independent image-subgroup directions, also with arbitrary original cell weights.'
]
remaining='The retained-root product and independent image-direction Haar averages are exactly identified with the original subgroup cube average, including weighted cells. The full iterated Cauchy-Schwarz induction connecting the original short-increment expression to this retained-root expression, the short-increment reduction, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 1004 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'Every direction has the explicit hypothesis that its first coordinate is the original subgroup element. Projection commutes with finite sums, so each root copy equals the original subset-sum vertex. The identity holds for every dimension, including zero.',
 'Averaging the original parameter group removes the unused increment tuple by the exact product Haar formula and the normalized constant mean, not by an unnormalized counting sum.',
 'Root response implies injectivity by projection to the first coordinate. Equiv.ofInjective therefore gives an actual bijection onto each image subgroup and preserves its normalized Haar mean.',
 'Equiv.piCongrRight combines the distinct direction-image bijections into the required dependent product equivalence. This reparameterizes independently averaged image-subgroup directions simultaneously without changing denominators.',
 'The weighted identity is linear in the original weights and hence holds even without positivity or normalization assumptions. No probability weights are discarded or replaced.',
 'Six theorems are individually kernel audited. The retained-root expression is identified exactly, but the full repeated elimination inequality connecting it to the initial density-weighted cube is still unproved. Bessel, inverse correlator existence and the final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-retained-root-cube-audit.py').write_text(source,encoding='utf-8')
print('Prepared one-module audit: six theorems.')
