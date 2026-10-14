from pathlib import Path
import re
source=Path('round-density-cube-gowers-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-density-cube-gowers'", "PREFIX = 'round-haar-difference-density'").replace("OLD = 'round-iterated-directional-cauchy'", "OLD = 'round-density-cube-gowers'")
counts={'1010':'1013','1013':'1016','995':'998','1004':'1007','4819':'4829'}
source=re.sub(r'\b(?:1010|1013|995|1004|4819)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=7','new_theorems=9').replace('new_theorem_count=7','new_theorem_count=9').replace('new_definitions=2','new_definitions=1')
source=source.replace('== 7\n    root','== 9\n    root').replace("'theorem_count': 7","'theorem_count': 9")
source=source.replace('len(set(names)) == 9','len(set(names)) == 10').replace('len(names) == 9','len(names) == 10').replace('new_axiom_reports=9','new_axiom_reports=10').replace('new_selected_report_count=9','new_selected_report_count=10')
modules=['Hindman168/HaarDifferenceDensity.lean','Hindman168/HaarIndependentDensities.lean','Hindman168/IndependentDifferenceCubeBound.lean']
components=[
 'The Haar density of the difference of two independent samples is defined by the actual autocorrelation. It is nonnegative, has total Haar average one, and inherits the original density upper bound. An exact expectation identity reparameterizes the two original samples by their difference.',
 'Product Haar means factor exactly, and independent coordinate difference densities factor into their one-coordinate densities. Thus d independent differences have joint density at most C^d when each original density is bounded by C.',
 'The actual cube expectation under two independent tuples of nonnegative normalized increment densities is bounded by C^d times the weighted subgroup Gowers value of dimension 2^d. This preserves the original cell probabilities and allows different densities in each cell and coordinate.'
]
remaining='Independent increment differences now have an exact Haar density representation and the actual weighted two-tuple cube expectation satisfies the C^d subgroup Gowers bound. Instantiation with the original short-interval pushforward densities and the analytic passage from harmonic laws to the periodized Haar cell model, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 1013 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'The difference convention is v-u, matching the paper increments. The density at a is the Haar mean of r(u)r(u+a). Its expectation identity follows by the actual additive translation equivalence, with no change of normalization.',
 'Nonnegativity and total mean one are derived from the original density assumptions. The upper bound uses only r(u+a)<=C and the original total mean one, so taking differences does not square the density bound.',
 'The product Haar identity explicitly accounts for the cardinality of the full function space and all coordinate denominators. Difference density factorization therefore expresses genuine independent coordinates.',
 'The joint density upper bound is C^d, including the zero-dimensional empty product. The final cube estimate explicitly assumes C>0 and arbitrary unit-bounded real test functions.',
 'The final theorem starts from the actual independently sampled two-tuple expectation, converts it exactly to its density representation and applies the previously proved density cube estimate. All cell probabilities are retained.',
 'Nine theorems and one definition are individually kernel audited. Short-interval pushforward density estimates and harmonic periodization errors are still needed for the original sampling laws. Bessel, inverse correlator existence and the final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-haar-difference-density-audit.py').write_text(source,encoding='utf-8')
print('Prepared three-module audit: nine theorems, one definition.')
