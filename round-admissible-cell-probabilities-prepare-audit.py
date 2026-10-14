from pathlib import Path
import re
p='round-admissible-cell-probabilities'
s=Path('round-interior-mass-limit-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-interior-mass-limit'",f"PREFIX = '{p}'").replace("OLD = 'round-master-endpoint-loss'","OLD = 'round-interior-mass-limit'")
counts={'1043':'1045','1045':'1046','1027':'1028','1036':'1037','4910':'4914'}
s=re.sub(r'\b(?:1043|1045|1027|1036|4910)\b',lambda m:counts[m[0]],s)
s=s.replace('len(set(names)) == 5','len(set(names)) == 4').replace('len(names) == 5','len(names) == 4').replace('== 5\n','== 4\n').replace("'theorem_count': 5","'theorem_count': 4")
s=s.replace('new_theorems=5','new_theorems=4').replace('new_axiom_reports=5','new_axiom_reports=4').replace('new_theorem_count=5','new_theorem_count=4').replace('new_selected_report_count=5','new_selected_report_count=4').replace('new_module_count=2','new_module_count=1')
modules=['Hindman168/AdmissibleCellProbabilities.lean']
components=['On a complete cell inside the original window, an inadmissible residue contributes zero to every integerMass-weighted test. The exact aligned interval sum consequently equals the sum over admissible residues only.','Dividing each actual admissible cell mass by the actual aligned interval mass yields nonnegative cell probabilities with sum exactly one, provided that original retained mass is positive.']
remaining='Admissible residue restriction and normalized actual cell probabilities are now proved, with positivity of the retained mass already available eventually at master scales. Connecting this probability law to the uniformized cyclic correlation, renormalization errors and wrapping errors remains, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','The zero contribution theorem uses the original integerMass cell formula with W dividing M and the actual coprimality condition; arbitrary real tests are permitted.','For each interval index in Ico a b, the global containment hypotheses imply cell containment inside the original harmonic window. Both M and q are positive.','The admissible-only sum is proved by removing exactly the zero summands from the existing exact aligned partition.','Cell probabilities are the actual integerMass cell sums divided by the actual interval sum. Positive retained mass is explicit before division and sum-one cancellation; it is not supplied as an inverse-theorem certificate.','Four new theorems are individually kernel audited. The cyclic correlation transfer and deep inverse inputs remain incomplete.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
