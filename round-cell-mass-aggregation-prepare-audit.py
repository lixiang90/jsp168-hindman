from pathlib import Path
import re
p='round-cell-mass-aggregation'
s=Path('round-integer-cell-mass-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-integer-cell-mass'",f"PREFIX = '{p}'").replace("OLD = 'round-residue-cell-parametrization'","OLD = 'round-integer-cell-mass'")
counts={'1033':'1035','1035':'1037','1017':'1019','1026':'1028','4887':'4890'}
s=re.sub(r'\b(?:1033|1035|1017|1026|4887)\b',lambda m:counts[m[0]],s)
s=s.replace('len(set(names)) == 5','len(set(names)) == 3').replace('len(names) == 5','len(names) == 3').replace('== 5\n','== 3\n').replace("'theorem_count': 5","'theorem_count': 3")
s=s.replace('new_theorems=5','new_theorems=3').replace('new_axiom_reports=5','new_axiom_reports=3').replace('new_theorem_count=5','new_theorem_count=3').replace('new_selected_report_count=5','new_selected_report_count=3')
modules=['Hindman168/CompleteResidueCellMassPositive.lean','Hindman168/CompleteResidueCellMassAggregate.lean']
components=['Every admissible nonempty complete cell at a positive left endpoint inside the original harmonic window has strictly positive integerMass. Multiplying its conditional error by this actual mass gives the unnormalized cell error.','Summing actual complete-cell errors over any finite indexed family gives total indexed cell mass times Mq/X, with no cell-count loss. This statement does not require or assert that the family partitions the original window.']
remaining='The actual integerMass complete cells have positive mass and a mass-weighted aggregate uniformization error bounded by total indexed cell mass times Mq/X. Construction of the global disjoint cell partition, deletion of partial endpoint cells, renormalization and wrapping errors still require assembly, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','Positive cell mass is proved from the actual reciprocal sum: q>0 supplies an index and the positive left endpoint makes every reciprocal positive. The original positive normalizer is retained.','The unnormalized error uses the proved strictly positive actual cell mass to justify denominator cancellation.','Aggregation is over a finite indexed family of original admissible cells. The bound is total indexed mass times Mq/X, not the number of cells. No disjointness or partition coverage is assumed or claimed; those remain required for the global law.','Three new theorems are individually kernel audited. The original target and deep missing inputs remain unchanged.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
