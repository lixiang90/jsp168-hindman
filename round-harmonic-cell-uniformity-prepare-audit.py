from pathlib import Path
import re
source=Path('round-prediction-modulus-cap-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-prediction-modulus-cap'", "PREFIX = 'round-harmonic-cell-uniformity'").replace("OLD = 'round-master-cyclic-quotients'", "OLD = 'round-prediction-modulus-cap'")
counts={'1027':'1029','1029':'1031','1011':'1013','1020':'1022','4864':'4873'}
source=re.sub(r'\b(?:1027|1029|1011|1020|4864)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=6','new_theorems=9').replace('new_theorem_count=6','new_theorem_count=9')
source=source.replace('== 6\n    root','== 9\n    root').replace("'theorem_count': 6","'theorem_count': 9")
source=source.replace('len(set(names)) == 6','len(set(names)) == 9').replace('len(names) == 6','len(names) == 9').replace('new_axiom_reports=6','new_axiom_reports=9').replace('new_selected_report_count=6','new_selected_report_count=9')
modules=['Hindman168/NormalizedHaarWeightError.lean','Hindman168/HarmonicCellUniformity.lean']
components=[
 'A positive finite weight bounded between l and u differs after normalization from the uniform density by at most (u-l)/l. Unit-bounded tests inherit this error. The normalized Haar test is identified exactly with its original weighted-sum ratio.',
 'For original harmonic weights 1/y with A<=y<=A+R and A>0, the normalized density and conditional expectation differ from uniform by at most R/A. The bounds preserve the actual reciprocal weights and their sum normalization.',
 'With original nonnegative cell probabilities summing to one and every cell left endpoint at least X>0, the weighted conditional harmonic expectation differs from the weighted uniform-cell expectation by at most R/X, independently of cell count.'
]
remaining='The local harmonic-to-uniform conditional density and test bounds are proved with error R/A, and original cell probabilities give total error at most R/X. Instantiation with the actual complete interval/residue cell partition, deletion of partial endpoint cells and wrapping errors, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain, along with assembling the subgroup inverse lemma. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 1029 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'The generic normalized-weight bound first proves l<=mean(w)<=u and strict positivity of that mean. It divides the absolute weight-minus-mean bound by this positive mean, so no denominator sign is assumed implicitly.',
 'Unit-bounded tests preserve the pointwise density error by absolute product bounds and the exact normalized finite sum inequality.',
 'The normalized Haar expression is proved equal to the original weighted-sum ratio using the nonzero finite cardinality. This identity does not silently replace the conditional normalization.',
 'For harmonic weights the reciprocal bounds are 1/(A+R) and 1/A. The resulting ratio simplifies exactly to R/A under A>0 and R>=0.',
 'The aggregate estimate preserves each cell probability. A common lower endpoint X controls every local error by R/X, so summing cannot introduce a factor equal to the number of cells.',
 'Nine theorems in two modules are individually kernel audited. The actual integerMass partition and partial-cell/wrapping comparisons still require assembly; Bessel, inverse correlator existence and the final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-harmonic-cell-uniformity-audit.py').write_text(source,encoding='utf-8')
print('Prepared two-module audit: nine theorems.')
