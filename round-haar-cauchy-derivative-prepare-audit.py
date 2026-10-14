from pathlib import Path
import re
source=Path('round-subgroup-gowers-root-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-subgroup-gowers-root'", "PREFIX = 'round-haar-cauchy-derivative'").replace("OLD = 'round-subgroup-cube-recursion'", "OLD = 'round-subgroup-gowers-root'")
counts={'992':'995','995':'998','977':'980','986':'989','4755':'4764'}
source=re.sub(r'\b(?:992|995|977|986|4755)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=10','new_theorems=9').replace('new_theorem_count=10','new_theorem_count=9').replace('new_definitions=2','new_definitions=0')
source=source.replace('== 10\n    root','== 9\n    root').replace("'theorem_count': 10","'theorem_count': 9")
source=source.replace('len(set(names)) == 12','len(set(names)) == 9').replace('len(names) == 12','len(names) == 9').replace('new_axiom_reports=12','new_axiom_reports=9').replace('new_selected_report_count=12','new_selected_report_count=9')
modules=['Hindman168/SubgroupCubeDerivative.lean','Hindman168/FiniteHaarCauchySchwarz.lean','Hindman168/SubgroupCubeMomentMonotone.lean']
components=[
 'The original real subgroup cube product distributes over pointwise multiplication, and its successor dimension is exactly the lower-dimensional multiplicative derivative. The normalized cube mean satisfies the corresponding derivative recursion.',
 'Normalized finite Haar means satisfy monotonicity and Cauchy-Schwarz. For nonempty finite types the square of a mean is bounded by the mean square, and a unit-bounded factor can be discarded with this inequality.',
 'Averaging subgroup Haar means over the ambient finite group preserves the original mean. Consequently the square of each dimension-d cube mean is bounded by the dimension-(d+1) cube mean, without a boundedness hypothesis on the real function.'
]
remaining='Actual derivative recursion, normalized Haar Cauchy-Schwarz and adjacent cube moment comparison are proved. Generalized Cauchy-Schwarz for the short-increment reduction, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 995 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'The multiplicative derivative is for real functions and uses the actual original cube product. Commutativity of the ambient additive group justifies the translated face identity.',
 'The derivative mean recursion uses the exact Fin.cons equivalence and exchanges the finite Haar means; it does not change cardinality denominators.',
 'The normalized Cauchy-Schwarz statement follows from the finite sum inequality divided by the square of the original cardinality. This statement allows empty finite types. Mean-square and unit-factor removal explicitly require nonemptiness.',
 'The ambient integral of a subgroup Haar mean equals the original integral by translation invariance, independently of subgroup index.',
 'Two applications of the normalized mean-square inequality to the exact successor square identity establish the adjacent cube moment bound for every natural dimension, including zero, and every real function. No sign or unit bound is assumed.',
 'Nine theorems are individually kernel audited. These results do not establish the required generalized short-increment estimate or Bessel theorem; inverse correlator existence and the final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-haar-cauchy-derivative-audit.py').write_text(source,encoding='utf-8')
print('Prepared three-module audit: nine theorems.')
