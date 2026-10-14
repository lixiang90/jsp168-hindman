from pathlib import Path
import re
source=Path('round-coprime-subgroup-sum-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-coprime-subgroup-sum'","PREFIX = 'round-subgroup-cube-average'").replace("OLD = 'round-native-correlation'","OLD = 'round-coprime-subgroup-sum'")
counts={'981':'983','983':'986','965':'968','974':'977','4709':'4721'}
source=re.sub(r'\b(?:981|983|965|974|4709|4709)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=6','new_theorems=8').replace('new_theorem_count=6','new_theorem_count=8').replace('new_definitions=1','new_definitions=4')
source=source.replace('== 6\n    root','== 8\n    root').replace("'theorem_count': 6","'theorem_count': 8")
source=source.replace('len(set(names)) == 7','len(set(names)) == 12').replace('len(names) == 7','len(names) == 12').replace('new_axiom_reports=7','new_axiom_reports=12').replace('new_selected_report_count=7','new_selected_report_count=12').replace('new_module_count=2','new_module_count=3')
modules=['Hindman168/FiniteHaarMean.lean','Hindman168/SubgroupCubeAverage.lean','Hindman168/SubgroupCubeCombination.lean']
components=[
 'Normalized finite Haar means are actual finite sums divided by cardinality, with constant normalization, additivity and absolute bound for unit-bounded functions on nonempty finite types.',
 'Actual subgroup cube products average h(x+sum of chosen directions) over every vertex subset, with the root Haar-uniform in the ambient finite abelian group and directions independently Haar-uniform in the actual subgroup. Cube product and mean absolute bounds and the constant-one normalization are proved.',
 'Finite cell-weighted cube means retain the original nonnegative cell probabilities summing to one. Their absolute bound is proved, and the actual weighted cube statistic is substituted into the coprime-subgroup combination theorem, retaining both prime-tuple and cell probabilities.'
]
remaining=('Actual finite subgroup cube averages and cell-weighted cube averages are now defined and bounded, and their absolute values satisfy the probability-weighted coprime-pair combination bound. These are cube means, not yet Gowers norms: nonnegativity in positive dimensions, root conventions and seminorm estimates remain. Next prove those properties and the short-increment Cauchy-Schwarz reduction, Bessel inverse input, cyclic-to-interval transfer and inverse correlators. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before editing. All 983 baseline hashes checked at registration, preserving prior proofs, original target, laws and fixed dependencies.',
 'The fixed mathlib tree has no Gowers-norm development found by the relevant file search. This increment builds actual finite averages directly from finite sums, rather than adding an assumed norm interface.',
 'A cube direction is an element of Fin d -> Q, and vertices are all finite subsets of Fin d. The product evaluates actual ambient-group additions using the subgroup inclusion; direction averaging therefore uses subgroup Haar measure and the root uses ambient Haar measure.',
 'Every group and subgroup is nonempty. Normalization of finiteHaarMean_const explicitly requires nonempty finite types, preventing division-by-zero normalization claims. The cube bound uses the absolute value of each real factor.',
 'Cell probabilities and prime-tuple probabilities are distinct finite weighted sums. The final combination theorem preserves both and charges only the original product probability of a noncoprime tuple pair, independently of both family cardinalities.',
 'The combined statistic is the absolute value of the actual cube mean. It is not called a Gowers norm, and no nonnegativity or 2^d-th root identity is asserted. Applying the paper Bessel inequality still requires actual norm construction and its theorem.',
 'Eight theorems and four definitions receive individual kernel axiom reports. Main inverse inputs and final target remain unproved; no unavoidable blocker is claimed.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-subgroup-cube-average-audit.py').write_text(source,encoding='utf-8')
print('Prepared three-module audit: eight theorems, four definitions.')
