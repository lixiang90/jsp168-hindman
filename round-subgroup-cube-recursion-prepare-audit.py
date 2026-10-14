from pathlib import Path
import re
source=Path('round-haar-correlation-square-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-haar-correlation-square'","PREFIX = 'round-subgroup-cube-recursion'").replace("OLD = 'round-subgroup-cube-average'","OLD = 'round-haar-correlation-square'")
counts={'986':'989','989':'992','971':'974','980':'983','4734':'4743'}
source=re.sub(r'\b(?:986|989|971|980|4734)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=12','new_theorems=9').replace('new_theorem_count=12','new_theorem_count=9').replace('new_definitions=1','new_definitions=0')
source=source.replace('== 12\n    root','== 9\n    root').replace("'theorem_count': 12","'theorem_count': 9")
source=source.replace('len(set(names)) == 13','len(set(names)) == 9').replace('len(names) == 13','len(names) == 9').replace('new_axiom_reports=13','new_axiom_reports=9').replace('new_selected_report_count=13','new_selected_report_count=9')
modules=['Hindman168/CubeProductSplitting.lean','Hindman168/FiniteHaarDirections.lean','Hindman168/SubgroupCubePositive.lean']
components=[
 'The actual vertex product splits on insertion of one coordinate into two faces. Injective coordinate maps preserve the product exactly. Applying these to Fin(d+1) gives the actual successor-dimensional cube product as two d-dimensional face products.',
 'Normalized Haar means over product types and successor direction functions are reindexed through actual product and Fin.cons equivalences, and three nested means are exactly reordered.',
 'Every positive-dimensional actual subgroup cube average is the mean square of subgroup-averaged face products. Hence every such cube average is nonnegative for arbitrary real functions, and the same holds after summing with nonnegative cell weights.'
]
remaining=('All positive-dimensional actual subgroup cube means now have an exact mean-square representation and proved nonnegativity, including weighted cells. Next define their positive Gowers roots and prove required norm estimates, short-increment Cauchy-Schwarz reduction, Bessel inverse input, cyclic-to-interval transfer and inverse correlators. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before editing. All 989 baseline hashes checked at registration, preserving previous proof sources, original target, laws and pins.',
 'Vertex splitting is proved for an actual powerset of an inserted finite coordinate set. The sum_insert side condition follows from subset membership in the old powerset. The two resulting face products have the original root and translated root.',
 'An injective coordinate map preserves the powerset product and vertex sums. Fin(d+1) is proved to be zero inserted into the successor image, so the dimension-splitting theorem is for the existing subgroupCubeProduct definition.',
 'Direction functions are reindexed by the true Fin.cons equivalence and exact finite Haar product formula. Denominators and cardinalities are preserved. Reordering nested finite means does not invoke an unproved measure or limit interchange.',
 'For each fixed d-dimensional direction vector, its face product is an arbitrary real function of the root. The already proved first-order subgroup correlation square identity applies to this function, giving a mean-square formula in dimension d+1.',
 'This proves all positive dimensions directly, without a sign bound on the original function. Dimension zero is deliberately excluded. Nonnegative cell-weighted sums inherit positivity without requiring cell probabilities to sum to one.',
 'Nine new theorems are individually kernel audited. Gowers roots, seminorm inequalities, Bessel/GTZ inverse inputs and the main arithmetic conclusion remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-subgroup-cube-recursion-audit.py').write_text(source,encoding='utf-8')
print('Prepared three-module audit: nine theorems.')
