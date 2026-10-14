from pathlib import Path
import re
source=Path('round-subgroup-cube-average-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-subgroup-cube-average'","PREFIX = 'round-haar-correlation-square'").replace("OLD = 'round-coprime-subgroup-sum'","OLD = 'round-subgroup-cube-average'")
counts={'983':'986','986':'989','968':'971','977':'980','4721':'4734'}
source=re.sub(r'\b(?:983|986|968|977|4721)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=8','new_theorems=12').replace('new_theorem_count=8','new_theorem_count=12').replace('new_definitions=4','new_definitions=1')
source=source.replace('== 8\n    root','== 12\n    root').replace("'theorem_count': 8","'theorem_count': 12")
source=source.replace('len(set(names)) == 12','len(set(names)) == 13').replace('len(names) == 12','len(names) == 13').replace('new_axiom_reports=12','new_axiom_reports=13').replace('new_selected_report_count=12','new_selected_report_count=13')
modules=['Hindman168/FiniteHaarIdentities.lean','Hindman168/SubgroupHaarSquare.lean','Hindman168/SubgroupCubeDimensionOne.lean']
components=[
 'Actual finite Haar averages satisfy equivalence change of variables, scalar multiplication, iterated-mean commutation, positivity and translation invariance.',
 'The actual subgroup averaging operator is invariant along subgroup translates. The mean of h(x)h(x+a) over ambient roots and subgroup directions is exactly the mean square of the subgroup average, so it is nonnegative for every real h.',
 'The original one-dimensional subgroupCubeProduct is proved equal to h(x)h(x+v0), and its direction mean is transferred through the actual equivalence (Fin 1 -> Q) equiv Q. Thus the previously defined one-dimensional subgroup cube mean equals the subgroup-average square and is nonnegative.'
]
remaining=('Exact finite Haar identities and the first-order subgroup square identity are now proved and matched to the existing cube definition. One-dimensional cube means are nonnegative without any sign condition on h. Next prove the higher-dimensional cube splitting/recursion and nonnegativity, then define the positive Gowers roots and prove needed estimates. Short-increment reduction, Bessel inverse input, cyclic-to-interval transfer, inverse correlators, coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 986 retained baseline hashes verified at registration. Prior proofs, original target, laws and fixed dependencies remain unchanged.',
 'Finite Haar change of variables uses an actual equivalence and equal cardinalities. Iterated mean commutation is an exact finite-sum identity with the same denominators, not an exchange of limiting operations.',
 'Subgroup translations reindex the actual subgroup Haar variables. Averaging the root translation and commuting finite averages gives the exact square identity; no sign bound or positivity of h is assumed.',
 'The square identity is connected to the previously defined cube mean rather than a newly convenient substitute. Finset(Fin 1) is explicitly enumerated and (Fin 1 -> Q) is reindexed using its true equivalence to Q.',
 'Nonnegativity is established only for dimension one in this increment. Higher-dimensional recurrence, norm roots and seminorm inequalities are not inferred from the base case without proof.',
 'Twelve theorems and one definition are individually kernel audited. Bessel/GTZ inverse inputs, coloring-derived targets and the full arithmetic conclusion remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-haar-correlation-square-audit.py').write_text(source,encoding='utf-8')
print('Prepared three-module audit: twelve theorems, one definition.')
