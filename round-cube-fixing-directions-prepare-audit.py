from pathlib import Path
import re
source=Path('round-invariant-factor-cauchy-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-invariant-factor-cauchy'", "PREFIX = 'round-cube-fixing-directions'").replace("OLD = 'round-gowers-dimension-monotone'", "OLD = 'round-invariant-factor-cauchy'")
counts={'1000':'1002','1002':'1004','984':'986','993':'995','4777':'4791'}
source=re.sub(r'\b(?:1000|1002|984|993|4777)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=5','new_theorems=11').replace('new_theorem_count=5','new_theorem_count=11').replace('new_definitions=0','new_definitions=3')
source=source.replace('== 5\n    root','== 11\n    root').replace("'theorem_count': 5","'theorem_count': 11")
source=source.replace('len(set(names)) == 5','len(set(names)) == 14').replace('len(names) == 5','len(names) == 14').replace('new_axiom_reports=5','new_axiom_reports=14').replace('new_selected_report_count=5','new_selected_report_count=14')
modules=['Hindman168/CubeVertexFixingDirections.lean','Hindman168/CubeCopyElimination.lean']
components=[
 'The original cube parameter group has explicit root and vertex-fixing additive homomorphisms. The latter translates the root by a and one selected increment by -a. It fixes every translated copy of any vertex containing the selected coordinate, and the empty vertex responds by a.',
 'Arbitrary finite products of translated copies of a unit-bounded vertex function are invariant under the full image subgroup of its fixing direction and remain unit-bounded. The exact subgroup Cauchy-Schwarz estimate therefore removes all these copies in one step. A separate exact estimate removes any bounded root-independent density along the root direction.'
]
remaining='The paper root and vertex-fixing directions, translated-copy invariance, and exact single-step density/copy elimination are proved. The full iterated Cauchy-Schwarz induction, identification of the retained root copies with a Haar cube, the short-increment reduction, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 1002 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'The cube vertex evaluation is defined on G times (Fin d to Q) by the original root plus the sum over the vertex. The two directions are explicit additive homomorphisms from Q; no surrogate action is assumed.',
 'For a selected coordinate belonging to the vertex, the added root and subtracted increment cancel exactly. The proof extends to any translated copy, and all parameter translations commute. The root vertex has response a.',
 'The root-only direction preserves the entire increment tuple and hence any density depending only on increments.',
 'Translated-copy products are invariant under every element of the image subgroup, using its actual preimage witness. Their absolute values are at most one for arbitrary finite copy families, including the empty family.',
 'The elimination estimates instantiate the already proved invariant-factor Cauchy-Schwarz theorem with those actual image subgroups. Finite enumerations of the image subgroups are explicit typeclass parameters; in the finite parameter group these exist. The remaining function is arbitrary.',
 'Eleven theorems and three definitions are individually kernel audited. This proves the direction and copy-removal mechanism, not the full iteration or final Haar-cube identification. Bessel, inverse correlator existence and the final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-cube-fixing-directions-audit.py').write_text(source,encoding='utf-8')
print('Prepared two-module audit: eleven theorems, three definitions.')
