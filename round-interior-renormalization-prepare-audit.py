from pathlib import Path
import re
p='round-interior-renormalization'
s=Path('round-admissible-cell-probabilities-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-admissible-cell-probabilities'",f"PREFIX = '{p}'").replace("OLD = 'round-interior-mass-limit'","OLD = 'round-admissible-cell-probabilities'")
counts={'1045':'1046','1046':'1048','1028':'1030','1037':'1039','4914':'4917'}
s=re.sub(r'\b(?:1045|1046|1028|1037|4914)\b',lambda m:counts[m[0]],s)
s=s.replace('len(set(names)) == 4','len(set(names)) == 3').replace('len(names) == 4','len(names) == 3').replace('== 4\n','== 3\n').replace("'theorem_count': 4","'theorem_count': 3")
s=s.replace('new_theorems=4','new_theorems=3').replace('new_axiom_reports=4','new_axiom_reports=3').replace('new_theorem_count=4','new_theorem_count=3').replace('new_selected_report_count=4','new_selected_report_count=3').replace('new_module_count=1','new_module_count=2')
modules=['Hindman168/FiniteRetainedProbabilityError.lean','Hindman168/MasterInteriorRenormalization.lean']
components=['For a finite probability weight, restricting to a positive-mass subset and renormalizing changes any unit-bounded test expectation by at most twice the deleted mass. The estimate includes both deletion and normalization errors.','For the actual original integerMass and aligned interior at master scales, the absolute difference between the full-window test and the normalized interior test tends to zero, for any stage-dependent unit-bounded test and varying ordered gap/pivot indices.']
remaining='The actual harmonic law now transfers to its normalized aligned interior with vanishing test error, and admissible normalized cell probabilities are proved. Connecting this law to the uniformized cyclic correlation and wrapping errors remains, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','The finite test bound uses nonnegative weights and absolute unit bounds. The renormalization theorem requires the original total exactly one and a strictly positive retained mass.','The proof splits the full sum over the subset and its difference, then bounds the deletion and rescaling contributions separately by the same deleted mass. No convergence of the tests themselves is required.','The original master specialization obtains total one and positive retained mass only on the already proved eventual sets. All stages, including zero normalizers or empty interiors, remain in the sequence; eventual comparison suffices.','The limiting bound is twice the actual deleted mass, already proved to vanish. Three new theorems are individually kernel audited; cyclic wrapping and inverse inputs remain open.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
