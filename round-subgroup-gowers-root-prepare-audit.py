from pathlib import Path
import re
source=Path('round-subgroup-cube-recursion-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-subgroup-cube-recursion'","PREFIX = 'round-subgroup-gowers-root'").replace("OLD = 'round-haar-correlation-square'","OLD = 'round-subgroup-cube-recursion'")
counts={'989':'992','992':'995','974':'977','983':'986','4743':'4755'}
source=re.sub(r'\b(?:989|992|974|983|4743)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=9','new_theorems=10').replace('new_theorem_count=9','new_theorem_count=10').replace('new_definitions=0','new_definitions=2')
source=source.replace('== 9\n    root','== 10\n    root').replace("'theorem_count': 9","'theorem_count': 10")
source=source.replace('len(set(names)) == 9','len(set(names)) == 12').replace('len(names) == 9','len(names) == 12').replace('new_axiom_reports=9','new_axiom_reports=12').replace('new_selected_report_count=9','new_selected_report_count=12')
modules=['Hindman168/SubgroupGowersRoot.lean','Hindman168/WeightedMomentThreshold.lean','Hindman168/SubgroupGowersWeightedBounds.lean']
components=[
 'Nonnegative real 2^d-th roots are constructed from the actual subgroup cube means. For positive d, their powers exactly recover those means and their values lie in [0,1] for unit-bounded functions. The same construction for weighted cells has the exact weighted power identity.',
 'A finite probability-weighted moment estimate proves that a global root at least delta forces total probability at least delta^(2^d)/2 on cells whose actual root is at least delta/2. The estimate is independent of the number of cells.',
 'The coprime-subgroup weighted combination estimate is instantiated with the actual weighted nonnegative Gowers roots, giving the full-group root plus the original noncoprime-pair probability as the error bound.'
]
remaining=('Actual nonnegative Gowers roots, their exact power identities, unit bounds, weighted good-cell mass estimate and root-level coprime subgroup combination are now proved. Triangle inequalities and the Bessel inverse input are not implied by this construction. Next establish required Cauchy-Schwarz estimates, short-increment reduction, Bessel input, cyclic-to-interval transfer and inverse correlators. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 992 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'The root exponent is the inverse real cast of the natural number 2^d. Its nonzero denominator is proved, and exact recovery of the original cube mean uses its previously established nonnegativity for d>0.',
 'The weighted global power equals the probability-weighted sum of cell powers exactly. The proof does not equate a weighted average of roots with the root of a weighted average.',
 'The threshold estimate is proved directly with original nonnegative finite weights summing to one. Below threshold each power is bounded by the threshold power; above threshold each power is at most one. For positive exponent, the half-threshold power is at most half the original power.',
 'The good-cell theorem is instantiated with the actual subgroup roots and yields delta^(2^d)/2, preserving the paper threshold and independence from cell count. No equal-weight reduction or discarded cell probabilities are used.',
 'The weighted combination estimate now applies to roots themselves, using their proved [0,1] bound. This still does not prove the Bessel theorem that relates individual subgroups to sums, and no triangle inequality or full seminorm package is asserted.',
 'Ten theorems and two definitions are individually kernel audited. Inverse correlator existence and the final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-subgroup-gowers-root-audit.py').write_text(source,encoding='utf-8')
print('Prepared three-module audit: ten theorems, two definitions.')
