from pathlib import Path
import re
source=Path('round-gowers-dimension-monotone-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-gowers-dimension-monotone'", "PREFIX = 'round-invariant-factor-cauchy'").replace("OLD = 'round-haar-cauchy-derivative'", "OLD = 'round-gowers-dimension-monotone'")
counts={'998':'1000','1000':'1002','982':'984','991':'993','4772':'4777'}
source=re.sub(r'\b(?:998|1000|982|991|4772)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=8','new_theorems=5').replace('new_theorem_count=8','new_theorem_count=5')
source=source.replace('== 8\n    root','== 5\n    root').replace("'theorem_count': 8","'theorem_count': 5")
source=source.replace('len(set(names)) == 8','len(set(names)) == 5').replace('len(names) == 8','len(names) == 5').replace('new_axiom_reports=8','new_axiom_reports=5').replace('new_selected_report_count=8','new_selected_report_count=5')
modules=['Hindman168/SubgroupInvariantFactorCauchy.lean','Hindman168/WeightedInvariantFactorCauchy.lean']
components=[
 'A real bounded factor invariant under a subgroup can be removed in one Cauchy-Schwarz step. The square of the original product mean is bounded by the square of the factor bound times the exact Haar subgroup autocorrelation of the remaining function.',
 'The same invariant-factor elimination is proved for arbitrary finite probability-weighted cells, with every original weight retained and a bound independent of the number of cells. The remaining function need not be bounded.'
]
remaining='One-step invariant-factor Cauchy-Schwarz elimination is proved for actual subgroup Haar means and arbitrary probability-weighted cells. Iteration along the paper root and vertex-fixing directions, the full short-increment reduction, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 1000 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'The fixed local paper identifies directions leaving individual factors invariant. The new elimination statement explicitly requires invariance under the actual subgroup translations; it does not assume the desired correlation estimate.',
 'A subgroup-invariant factor pulls outside the subgroup Haar mean. The ambient integral identity then replaces the remaining factor by its exact subgroup conditional mean, preserving normalization.',
 'Normalized Cauchy-Schwarz bounds the product mean squared by C squared times the mean square of the conditional mean. The previously proved exact square identity converts the latter into the original subgroup autocorrelation.',
 'The general bounded-factor inequality needs no sign hypothesis on the remaining function. The absolute-value bound on the removed factor is explicit. No unproved seminorm properties are used.',
 'The weighted theorem first applies the finite probability mean-square inequality and then the single-cell elimination. Original weights remain unchanged; all factors share the stated uniform bound C, which is independent of cell count.',
 'Five theorems in two modules are individually kernel audited. The paper requires repeated elimination of vertex copies along commuting directions; that iteration is not yet proved. Bessel, inverse correlator existence and the final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-invariant-factor-cauchy-audit.py').write_text(source,encoding='utf-8')
print('Prepared two-module audit: five theorems.')
