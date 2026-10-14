from pathlib import Path
import re
source=Path('round-haar-cauchy-derivative-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-haar-cauchy-derivative'", "PREFIX = 'round-gowers-dimension-monotone'").replace("OLD = 'round-subgroup-gowers-root'", "OLD = 'round-haar-cauchy-derivative'")
counts={'995':'998','998':'1000','980':'982','989':'991','4764':'4772'}
source=re.sub(r'\b(?:995|998|980|989|4764)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=9','new_theorems=8').replace('new_theorem_count=9','new_theorem_count=8').replace('new_module_count=3','new_module_count=2')
source=source.replace('== 9\n    root','== 8\n    root').replace("'theorem_count': 9","'theorem_count': 8")
source=source.replace('len(set(names)) == 9','len(set(names)) == 8').replace('len(names) == 9','len(names) == 8').replace('new_axiom_reports=9','new_axiom_reports=8').replace('new_selected_report_count=9','new_selected_report_count=8')
modules=['Hindman168/SubgroupGowersDimensionMonotone.lean','Hindman168/WeightedSubgroupGowersMonotone.lean']
components=[
 'Actual subgroup Gowers roots are increasing with positive dimension. The original ambient Haar mean is the zero-dimensional cube mean and its absolute value is bounded by every positive-dimensional subgroup Gowers root.',
 'For arbitrary nonnegative finite probability weights, the square of the weighted mean is bounded by the weighted mean square. This yields adjacent cube-moment comparison and dimension monotonicity for the actual weighted subgroup Gowers roots, preserving the original cell probabilities.'
]
remaining='Actual single-cell and probability-weighted subgroup Gowers roots now have proved positive-dimension monotonicity; the single-cell roots control the ambient mean. Generalized Cauchy-Schwarz for the short-increment reduction, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 998 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'Adjacent dimension comparison raises the actual roots to the same strictly positive natural power 2^(d+1), uses their exact power identities and the previously established cube-moment inequality, then uses monotonicity of powers on nonnegative reals.',
 'The dimension comparison explicitly requires positive starting dimension. The zero-dimensional cube mean is separately identified with the signed ambient mean; no invalid nonnegative root assertion for dimension zero is made.',
 'The ambient mean bound uses the square inequality from zero to one dimension and then positive-dimension monotonicity. It holds without a unit bound or sign assumption on the function.',
 'The weighted mean-square inequality is proved by expanding the nonnegative weighted variance. Every original probability weight remains present, and the total probability one assumption is explicit.',
 'The weighted root comparison uses the root of the weighted cube mean and its exact power identity, never the weighted average of roots. It applies to arbitrary finite probability weights and arbitrary real functions.',
 'Eight theorems in two modules are individually kernel audited. These statements do not establish generalized short-increment Cauchy-Schwarz, Bessel, inverse correlator existence or the final target.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-gowers-dimension-monotone-audit.py').write_text(source,encoding='utf-8')
print('Prepared two-module audit: eight theorems.')
