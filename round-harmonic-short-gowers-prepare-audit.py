from pathlib import Path
import re
p='round-harmonic-short-gowers'
s=Path('round-integer-short-gowers-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-integer-short-gowers'",f"PREFIX = '{p}'").replace("OLD = 'round-averaged-short-wrapping'","OLD = 'round-integer-short-gowers'")
counts={'1054':'1055','1055':'1057','1037':'1039','1046':'1048','4934':'4936'}
s=re.sub(r'\b(?:1054|1055|1037|1046|4934)\b',lambda m:counts[m[0]],s)
s=s.replace('new_module_count=1','new_module_count=2')
modules=['Hindman168/WeightedHarmonicCyclicCells.lean','Hindman168/HarmonicShortCubeGowersBound.lean']
components=['Actual admissible integerMass cell conditional expectations, averaged by nonnegative sum-one cell weights, differ from their affine cyclic Haar averages by at most the common cell width divided by X.','The actual weighted conditional harmonic short-cube average is bounded by (2J)^d times the weighted subgroup Gowers value of order 2^d, plus 4d/J and M*a*n/X. This combines harmonic uniformization, signed cyclic wrapping and the finite Gowers bound.']
remaining='The weighted original integerMass conditional short-cube average now has the Gowers bound with explicit wrapping and harmonic uniformization errors. Applying the exact admissible aligned-cell probability decomposition and master rate limits to obtain the global original-law estimate remains, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','Each conditional harmonic cell is an actual intervalResidueSet with original integerMass, admissible residue, positive original normalizer and containment in the original harmonic window.','The weighted uniformization error uses the common lower endpoint X>0 and the actual cell width M*q. Nonnegative sum-one cell weights prevent a cell-count loss.','The short-cube test is unit-bounded by two finite mean bounds and the full vertex-product bound. Positive short interval length is used before averaging.','The final bound combines the verified conditional harmonic comparison with the verified integer short-cube Gowers bound. The errors 4d/J and M*a*n/X remain explicit.','Two new theorems are individually kernel audited. Global original-law specialization, Bessel and inverse inputs remain unfinished and are not assumed as certificates.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
