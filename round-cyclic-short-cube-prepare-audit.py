from pathlib import Path
import re
source=Path('round-uniform-tuple-expectation-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-uniform-tuple-expectation'", "PREFIX = 'round-cyclic-short-cube'").replace("OLD = 'round-uniform-image-density'", "OLD = 'round-uniform-tuple-expectation'")
counts={'1019':'1022','1022':'1024','1004':'1006','1013':'1015','4846':'4851'}
source=re.sub(r'\b(?:1019|1022|1004|1013|4846)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=7','new_theorems=5').replace('new_theorem_count=7','new_theorem_count=5').replace('new_definitions=1','new_definitions=0').replace('new_module_count=3','new_module_count=2')
source=source.replace('== 7\n    root','== 5\n    root').replace("'theorem_count': 7","'theorem_count': 5")
source=source.replace('len(set(names)) == 8','len(set(names)) == 5').replace('len(names) == 8','len(names) == 5').replace('new_axiom_reports=8','new_axiom_reports=5').replace('new_selected_report_count=8','new_selected_report_count=5')
modules=['Hindman168/UniformImageCubeBound.lean','Hindman168/CyclicShortCubeBound.lean']
components=[
 'Uniform-image cube estimates are proved for arbitrary finite nonempty source types with an explicit ambient/source cardinality-ratio bound, preserving coordinatewise injective maps and original cell probabilities.',
 'For q dividing a positive modulus m, the original q-multiple subgroup has cardinality m/q. The explicit short interval map u -> q*u in ZMod(q*n) is instantiated into the weighted cube theorem with source length floor(n/J) and bound (2J)^d.',
 'The subgroup cube vertices are expanded exactly to x + q sum(v_j) - q sum(u_j). The resulting bound is stated directly for these original cyclic short-increment vertices and the actual q-multiple subgroup Gowers value of dimension 2^d.'
]
remaining='The explicit cyclic q-multiple short-increment cube estimate, its original vertex formula, divisor subgroup cardinality and original cell weights are proved. Instantiation with master-scale quotient parameters and the harmonic-to-periodized Haar comparison, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 1022 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'The uniform-image estimate keeps the original source sampling laws and uses only the explicit cardinality ratio, injectivity, nonnegative normalized cell weights, and unit bounds on the test functions.',
 'The divisor cardinality theorem reduces m=q*n using the actual divisibility witness. Positivity of m and q proves positivity of n before applying the explicit subgroup bijection.',
 'The cyclic estimate supplies the concrete shortened map u -> q*u, its proved injectivity, the proved subgroup size n, and the exact floor-length ratio bound. No injective map remains as an unverified hypothesis in this concrete statement.',
 'The vertex identity expands subgroup coercions and subtraction, then finite sums of q-multiples. It preserves the paper order v-u and retains the actual cyclic modulus q*n.',
 'Lean inference initially exceeded its default computation budget on the concrete application; explicit arguments resolved this without changing heartbeat limits or proof assumptions.',
 'Five theorems in two modules are individually kernel audited. The cyclic finite model is instantiated, while master-scale substitution, harmonic periodization errors, Bessel and inverse inputs, and the final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-cyclic-short-cube-audit.py').write_text(source,encoding='utf-8')
print('Prepared two-module audit: five theorems.')
