from pathlib import Path
import re
source=Path('round-averaged-copy-elimination-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-averaged-copy-elimination'", "PREFIX = 'round-iterated-directional-cauchy'").replace("OLD = 'round-retained-root-cube'", "OLD = 'round-averaged-copy-elimination'")
counts={'1005':'1007','1007':'1010','989':'992','998':'1001','4801':'4810'}
source=re.sub(r'\b(?:1005|1007|989|998|4801)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=4','new_theorems=8').replace('new_theorem_count=4','new_theorem_count=8').replace('new_definitions=0','new_definitions=1').replace('new_module_count=2','new_module_count=3')
source=source.replace('== 4\n    root','== 8\n    root').replace("'theorem_count': 4","'theorem_count': 8")
source=source.replace('len(set(names)) == 4','len(set(names)) == 9').replace('len(names) == 4','len(names) == 9').replace('new_axiom_reports=4','new_axiom_reports=9').replace('new_selected_report_count=4','new_selected_report_count=9')
modules=['Hindman168/HaarDyadicPower.lean','Hindman168/IteratedDirectionalCauchy.lean','Hindman168/IteratedRootCubeBound.lean']
components=[
 'Normalized Haar and finite probability-weighted averages satisfy the dyadic-power Jensen inequality for every real function and every exponent 2^n, including n=0.',
 'A complete induction removes any finite family of real unit-bounded factors, each invariant along its assigned injective additive direction in a finite abelian group. The initial mean to power 2^n is bounded by the recursively defined iterated direction-difference mean; the proof derives all required invariance and bounds for doubled factors.',
 'When every direction has the original subgroup root response, the recursive mean equals the actual original subgroup cube mean. The resulting complete iterated estimate holds with original probability weights, and taking the exact positive-dimensional root gives the actual weighted Gowers bound.'
]
remaining='The complete abstract finite-direction Cauchy-Schwarz induction, its exact identification with original root subgroup cubes, and the weighted Gowers-root bound are proved. Instantiation with the normalized density and all nonroot vertices, the complete short-increment reduction, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 1007 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'Dyadic-power Jensen includes signed real functions. The n=0 case is equality and the n=1 case is mean-square. Higher powers are nonnegative before squaring an inequality, so no invalid squaring of a signed bound occurs.',
 'The iterated directional mean is defined by finite recursive averages of multiplicative derivatives. This is a concrete definition, not an assumption of the desired estimate.',
 'The full induction first removes the first invariant factor by actual image-subgroup Cauchy-Schwarz and an injective-direction Haar equivalence. It then raises the nonnegative squared left side and applies dyadic-power Jensen to the new direction average.',
 'Every remaining factor is replaced by its actual multiplicative derivative. Unit bounds follow by multiplying absolute values, and invariance follows from commutativity of the original additive group. The induction hypothesis applies to these explicitly constructed factors.',
 'For root-response directions, induction with the original cube derivative identity identifies the recursive mean exactly with the original subgroup cube mean. No seminorm triangle inequality or external inverse theorem is assumed.',
 'Probability-weighted dyadic Jensen preserves every original cell weight. The positive-dimensional Gowers corollary uses the even exponent to remove the absolute value and the proved exact weighted root power identity.',
 'Eight theorems and one definition are individually kernel audited. The complete abstract iteration is proved; the paper-specific density and nonroot vertex packaging and analytic short-increment comparison remain. Bessel, inverse correlator existence and the final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-iterated-directional-cauchy-audit.py').write_text(source,encoding='utf-8')
print('Prepared three-module audit: eight theorems, one definition.')
