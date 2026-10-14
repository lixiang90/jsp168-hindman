from pathlib import Path
import re
p='round-aligned-global-gowers'
s=Path('round-cell-disintegration-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-cell-disintegration'",f"PREFIX = '{p}'").replace("OLD = 'round-harmonic-short-gowers'","OLD = 'round-cell-disintegration'")
counts={'1057':'1058','1058':'1059','1040':'1041','1049':'1050','4938':'4939'}
s=re.sub(r'\b(?:1057|1058|1040|1049|4938)\b',lambda m:counts[m[0]],s)
s=s.replace('len(set(names)) == 2','len(set(names)) == 1').replace('len(names) == 2','len(names) == 1').replace('== 2\n','== 1\n').replace("'theorem_count': 2","'theorem_count': 1")
s=s.replace('new_theorems=2','new_theorems=1').replace('new_axiom_reports=2','new_axiom_reports=1').replace('new_theorem_count=2','new_theorem_count=1').replace('new_selected_report_count=2','new_selected_report_count=1')
modules=['Hindman168/AlignedGlobalShortCubeBound.lean']
components=['The normalized actual integerMass short-cube average on an aligned retained interval is bounded by (2J)^d times the weighted subgroup Gowers quantity plus 4d/J and R/X. The finite cell index and weights are explicitly constructed from the interval indices, admissible residues and original cell masses, rather than supplied as arbitrary probability data.']
remaining='The global aligned retained-interval harmonic short-cube estimate now uses the explicitly constructed actual cell law. Transfer back to the full original window and specialization of all errors and quotient geometry to the master scales remains, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','The cell index is the actual finite product of Ico l u and admissible residues in Fin M. The index is neither arbitrary nor assumed to partition the interval.','Each weight is the original integerMass cell sum divided by the actual retained interval mass. Nonnegativity and sum one are derived from previously proved original-law results and the explicit positive retained mass hypothesis.','Finite subtype summation is converted exactly to the double interval/residue sum. Exact disintegration then rewrites the weighted conditional test as the normalized retained interval test.','The weighted harmonic short-cube theorem is applied with cell endpoints and admissibility derived from index membership. The resulting Gowers quantity uses the actual cell law and actual affine cyclic observables.','One new global theorem is individually kernel audited. The full-window transfer and master specialization remain separate work; Bessel and inverse inputs are not assumed.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
