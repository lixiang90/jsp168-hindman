from pathlib import Path
import re
source=Path('round-harmonic-cell-uniformity-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-harmonic-cell-uniformity'", "PREFIX = 'round-residue-cell-parametrization'").replace("OLD = 'round-prediction-modulus-cap'", "OLD = 'round-harmonic-cell-uniformity'")
counts={'1029':'1031','1031':'1033','1013':'1015','1022':'1024','4873':'4882'}
source=re.sub(r'\b(?:1029|1031|1013|1022|4873)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=9','new_theorems=8').replace('new_theorem_count=9','new_theorem_count=8').replace('new_definitions=0','new_definitions=1')
source=source.replace('== 9\n    root','== 8\n    root').replace("'theorem_count': 9","'theorem_count': 8")
source=source.replace("old.AXIOM_FREE | {'Hindman168.intervalResidueParent'}", "old.AXIOM_FREE | {'Hindman168.intervalResidueParent', 'Hindman168.completeResidueCellPoint'}")
modules=['Hindman168/CompleteResidueCell.lean','Hindman168/CompleteResidueCellHarmonic.lean']
components=[
 'The original complete interval/residue cell in [kMq,(k+1)Mq) with residue r mod M has explicit coordinates kMq+r+Mt for t in Fin q. Bounds, residue identity, injectivity and surjectivity prove its exact cardinality q.',
 'Every sum on the original integer residue cell is reindexed exactly by these coordinates. The original conditional harmonic weighted-sum ratio consequently differs from the uniform coordinate expectation by at most Mq/(kMq) when the cell lies to the right of zero.'
]
remaining='The actual complete interval/residue cell has an explicit bijection with Fin(R/M), exact sum reindexing and the conditional harmonic-to-uniform error bound. Original integerMass cell probabilities and admissible-residue filtering, partial endpoint cell deletion and wrapping errors still require assembly, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 1031 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'The cell is the existing intervalResidueSet with the original half-open endpoints and residue condition. The coordinate map is explicit; no change of the underlying integer set is introduced.',
 'The interval and residue proofs retain arbitrary integer cell index k. Positive M and the Fin bounds on r and t ensure the map lies inside the cell; injectivity follows from multiplication by positive M.',
 'Surjectivity uses the actual Euclidean quotient y/M minus kq. The cell bounds and residue identity show this integer is between zero and q-1 before converting it to a natural Fin coordinate.',
 'Cardinality and finite-sum reindexing use the established bijection, with no asymptotic or counting approximation.',
 'The harmonic theorem assumes q>0 and positive real left endpoint before applying the conditional weighted-sum ratio estimate. Its left side is the sum over the original integer cell, while its uniform side is exactly the Fin q coordinate mean.',
 'Eight theorems and one definition are individually kernel audited. Original integerMass probabilities and unit-residue selection, endpoint deletion and wrapping errors, Bessel and inverse inputs, and the final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-residue-cell-parametrization-audit.py').write_text(source,encoding='utf-8')
print('Prepared two-module audit: eight theorems, one definition.')
