from pathlib import Path
import re
p='round-master-endpoint-loss'
s=Path('round-aligned-endpoints-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-aligned-endpoints'",f"PREFIX = '{p}'").replace("OLD = 'round-cell-partition'","OLD = 'round-aligned-endpoints'")
counts={'1039':'1041','1041':'1043','1023':'1025','1032':'1034','4901':'4905'}
s=re.sub(r'\b(?:1039|1041|1023|1032|4901)\b',lambda m:counts[m[0]],s)
s=s.replace('len(set(names)) == 6','len(set(names)) == 4').replace('len(names) == 6','len(names) == 4').replace('== 6\n','== 4\n').replace("'theorem_count': 6","'theorem_count': 4")
s=s.replace('new_theorems=6','new_theorems=4').replace('new_axiom_reports=6','new_axiom_reports=4').replace('new_theorem_count=6','new_theorem_count=4').replace('new_selected_report_count=6','new_selected_report_count=4')
modules=['Hindman168/AlignedInteriorMassCrude.lean','Hindman168/MasterAlignedEndpointLoss.lean']
components=['Under the original boundary geometry the reciprocal harmonic normalizer is at most W, by the proved unit-density lower bound and positivity of Euler totient. The actual aligned endpoint deletion mass is at most 2W(R+1)/X.','Along the original MasterParameterConditions with varying gap and pivot indices in their original eventual order, the actual deleted integerMass tends to zero. Every uniformly unit-bounded stage-dependent test on the deleted set has absolute weighted sum tending to zero.']
remaining='Aligned endpoint deletion and its effect on unit-bounded tests now tend to zero along the actual master scales. Admissible-residue restriction, assembly and renormalization of cell probabilities, and wrapping errors remain to connect, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','The normalizer reciprocal bound follows from the actual totient-density lower bound, with positive modulus and the explicit existing logarithmic geometry.','The deleted mass bound applies to the exact original integer window minus the explicit aligned interval. It is dominated by twice the existing master endpoint ratio with divisor budget K=1.','Convergence uses only the original MasterParameterConditions and the eventual gap/pivot order. Indices may vary with stage. No inverse theorem, cell probability hypothesis or new asymptotic assumption is inserted.','The test convergence is proved for any stage-dependent function bounded in absolute value by one, using nonnegative original integerMass at every stage. Zero-normalizer stages are retained.','Four new theorems are individually kernel audited. The global conditional cell law and deep inverse inputs remain unfinished.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
