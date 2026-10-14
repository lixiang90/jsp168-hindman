from pathlib import Path
import re
source=Path('round-retained-root-cube-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-retained-root-cube'", "PREFIX = 'round-averaged-copy-elimination'").replace("OLD = 'round-cube-fixing-directions'", "OLD = 'round-retained-root-cube'")
counts={'1004':'1005','1005':'1007','987':'989','996':'998','4797':'4801'}
source=re.sub(r'\b(?:1004|1005|987|996|4797)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=6','new_theorems=4').replace('new_theorem_count=6','new_theorem_count=4').replace('new_module_count=1','new_module_count=2')
source=source.replace('== 6\n    root','== 4\n    root').replace("'theorem_count': 6","'theorem_count': 4")
source=source.replace('len(set(names)) == 6','len(set(names)) == 4').replace('len(names) == 6','len(names) == 4').replace('new_axiom_reports=6','new_axiom_reports=4').replace('new_selected_report_count=6','new_selected_report_count=4')
modules=['Hindman168/AveragedInvariantFactorCauchy.lean','Hindman168/AveragedCubeCopyElimination.lean']
components=[
 'Invariant-factor Cauchy-Schwarz elimination now retains arbitrary previously introduced finite Haar variables and the original probability-weighted cells. Two normalized mean-square inequalities move the square inside these averages before the exact subgroup elimination step.',
 'The averaged elimination is reparameterized through each injective root-response direction back to the original subgroup. Its concrete instances remove a root-independent density or every translated copy of a selected nonroot vertex, with all previous direction variables and cell weights unchanged.'
]
remaining='Averaged density and vertex-copy elimination steps now retain all previous finite Haar variables and original cell probabilities, with new directions reparameterized by the original subgroup. The full iterated Cauchy-Schwarz induction and exponent accounting connecting the initial density-weighted cube to the identified retained-root cube, the short-increment reduction, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 1005 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'The outer parameter type is arbitrary finite and nonempty, so it can include all previously introduced independent directions. The proof uses the actual normalized Haar mean and original nonnegative probability weights summing to one.',
 'The square is first moved inside the cell average by weighted mean-square and then inside the old-direction average by Haar mean-square. The single-stage invariant-factor estimate is applied only after both justified inequalities.',
 'The explicit root-response hypothesis yields the actual direction-image Haar equivalence. Reparameterization returns precisely one new original-subgroup variable, retaining every old variable and every cell weight.',
 'For vertex-copy elimination, the removed product may contain an arbitrary finite family of shifts depending on both the cell and old parameters. All copies of the chosen vertex are invariant under its fixing direction and jointly unit-bounded.',
 'For density elimination, the density may depend on the cell, old parameters and the increment tuple. It is independent of the root, with the uniform absolute bound C explicit. The remaining function is unrestricted.',
 'Four theorems in two modules are individually kernel audited. The recurrence ingredients are proved, but the complete repeated-elimination induction and its exponent accounting are not yet established. Bessel, inverse correlator existence and the final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-averaged-copy-elimination-audit.py').write_text(source,encoding='utf-8')
print('Prepared two-module audit: four theorems.')
