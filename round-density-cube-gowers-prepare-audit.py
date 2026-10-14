from pathlib import Path
import re
source=Path('round-iterated-directional-cauchy-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-iterated-directional-cauchy'", "PREFIX = 'round-density-cube-gowers'").replace("OLD = 'round-averaged-copy-elimination'", "OLD = 'round-iterated-directional-cauchy'")
counts={'1007':'1010','1010':'1013','992':'995','1001':'1004','4810':'4819'}
source=re.sub(r'\b(?:1007|1010|992|1001|4810)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=8','new_theorems=7').replace('new_theorem_count=8','new_theorem_count=7').replace('new_definitions=1','new_definitions=2')
source=source.replace('== 8\n    root','== 7\n    root').replace("'theorem_count': 8","'theorem_count': 7")
modules=['Hindman168/IndexedRootGowersBound.lean','Hindman168/DensityCubeFactors.lean','Hindman168/DensityCubeGowersBound.lean']
components=[
 'The complete weighted root Gowers bound is reindexed by any nonempty finite factor type. The exact direction count remains its finite cardinality.',
 'The actual density-weighted cube is factored using all subsets of Fin d: the empty subset contributes the root-independent density and every nonempty subset its vertex function. Explicit root and vertex-fixing directions give all required invariance and root-response properties; the product identity exactly recovers the original cube.',
 'The original probability-weighted density cube mean is bounded in absolute value by C times the actual weighted subgroup Gowers value of dimension 2^d whenever the density is bounded by C>0 and the real vertex functions are unit-bounded. The constant is independent of cell count and preserves all original weights.'
]
remaining='The paper-specific finite Haar density-weighted cube to subgroup U^(2^d) bound is proved, with uniform constant equal to the density bound and original cell probabilities retained. The analytic passage from original harmonic short-increment laws to the finite Haar density model, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 1010 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'A finite factor type is reindexed by an actual equivalence from Fin of its cardinality. Product reindexing is exact, so the induction retains the original number of directions.',
 'All subsets of Fin d index the factors. The empty subset contributes the normalized density, not an extra vertex function. The original root function remains outside the factor product. The total number of factors is exactly 2^d, also for d=0.',
 'For each nonempty subset, its minimum element supplies a valid vertex-fixing coordinate. The corresponding direction is an explicit additive homomorphism and has root response a. The density uses the root-only direction.',
 'Factor bounds and invariance are proved before applying the complete iterated estimate. Separating the empty subset in the product proves the exact density times original cube product identity.',
 'For C>0, the density is divided by C, and its unit bound follows from the original absolute bound. Linearity of both Haar means and the weighted sum restores C exactly; positivity justifies its absolute value. No sign assumption on density or vertex function is required.',
 'The final bound is for the actual weighted subgroup Gowers root in dimension 2^d, with the original weights nonnegative and summing to one. It does not replace a weighted root by an average of roots.',
 'Seven theorems and two definitions are individually kernel audited. The finite Haar density-model estimate is complete. The original harmonic-to-periodic comparison, Bessel and inverse inputs, and final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-density-cube-gowers-audit.py').write_text(source,encoding='utf-8')
print('Prepared three-module audit: seven theorems, two definitions.')
