from pathlib import Path
import re
source=Path('round-haar-difference-density-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-haar-difference-density'", "PREFIX = 'round-uniform-image-density'").replace("OLD = 'round-density-cube-gowers'", "OLD = 'round-haar-difference-density'")
counts={'1013':'1016','1016':'1019','998':'1001','1007':'1010','4829':'4838'}
source=re.sub(r'\b(?:1013|1016|998|1007|4829)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=9','new_theorems=8').replace('new_theorem_count=9','new_theorem_count=8')
source=source.replace('== 9\n    root','== 8\n    root').replace("'theorem_count': 9","'theorem_count': 8")
source=source.replace('len(set(names)) == 10','len(set(names)) == 9').replace('len(names) == 10','len(names) == 9').replace('new_axiom_reports=10','new_axiom_reports=9').replace('new_selected_report_count=10','new_selected_report_count=9')
modules=['Hindman168/UniformImageHaarDensity.lean','Hindman168/ShortIntervalDensityBound.lean','Hindman168/ShortIntervalDifferenceCubeBound.lean']
components=[
 'The actual Haar density of a uniform injective finite image is constructed as the ambient/source cardinality ratio on its image and zero elsewhere. Its exact expectation agrees with the original uniform source expectation, it is nonnegative, and it has Haar mean one.',
 'For positive J and nonzero floor(m/J), the exact cardinality ratio m/floor(m/J) is at most 2J. Natural reduction of a length-L interval into ZMod m is injective whenever L<=m and m is nonzero.',
 'Independent uniform images of intervals of length floor(card(Q)/J) therefore give the original density-weighted difference-cube bound with constant (2J)^d and the actual subgroup Gowers dimension 2^d, retaining all cell probabilities.'
]
remaining='Uniform injective-image Haar densities, their exact source expectation identity, the floor-length 2J bound and the resulting (2J)^d difference-cube estimate are proved. Identification of the original q-multiple subgroup interval maps and simultaneous tuple pushforward expectations, the harmonic-to-periodized Haar comparison, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 1016 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'The density is explicit and uses the original source and ambient cardinalities. The expectation identity assumes an injective source map and nonempty source and ambient finite types, justifying the cardinality divisions.',
 'The floor-ratio estimate requires positive J and a nonempty short interval. It derives m<=2J floor(m/J) from Euclidean division with its remainder bound, then divides by the strictly positive floor length.',
 'The ZMod interval injection proof applies the actual residue value map to equality and uses both interval entries being less than the modulus. No wrap-free injectivity is assumed without a length bound.',
 'The difference-cube theorem instantiates the previous independent-density estimate with these constructed densities. Normalization is proved from source injectivity and the nonzero floor length; the density bound is 2J.',
 'The final statement retains the density-weighted Haar tuple expression and arbitrary original cell weights. Simultaneous tuple pushforward rewriting and the identification of the original multiple-subgroup map are not claimed complete.',
 'Eight theorems and one definition are individually kernel audited. Harmonic periodization errors, Bessel and inverse inputs, and the final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-uniform-image-density-audit.py').write_text(source,encoding='utf-8')
print('Prepared three-module audit: eight theorems, one definition.')
