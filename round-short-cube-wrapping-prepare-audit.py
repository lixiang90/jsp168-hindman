from pathlib import Path
import re
p='round-short-cube-wrapping'
s=Path('round-cyclic-wrap-bound-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-cyclic-wrap-bound'",f"PREFIX = '{p}'").replace("OLD = 'round-cyclic-cell-coordinates'","OLD = 'round-cyclic-wrap-bound'")
counts={'1049':'1051','1051':'1052','1033':'1034','1042':'1043','4925':'4928'}
s=re.sub(r'\b(?:1049|1051|1033|1042|4925)\b',lambda m:counts[m[0]],s)
s=s.replace('len(set(names)) == 4','len(set(names)) == 3').replace('len(names) == 4','len(names) == 3').replace('== 4\n','== 3\n').replace("'theorem_count': 4","'theorem_count': 3")
s=s.replace('new_theorems=4','new_theorems=3').replace('new_axiom_reports=4','new_axiom_reports=3').replace('new_theorem_count=4','new_theorem_count=3').replace('new_selected_report_count=4','new_selected_report_count=3').replace('new_module_count=2','new_module_count=1')
modules=['Hindman168/ShortCubeWrapBound.lean']
components=['Every short-cube vertex shift a*sum(v_j-u_j), with u and v in Fin L, has absolute value at most d*a*L. For L=floor(q/(J*a)), the resulting cyclic wrapping bound is at most 4d/J.','For the full product over all subsets of Fin d, the actual affine cyclic root average and integer short-cube root average differ by at most 4d/J, uniformly in the two short increment tuples, cell index, residue and multiplier.']
remaining='The full short-cube vertex product has a proved pointwise-in-increment-tuples cyclic wrapping error at most 4d/J. Averaging the increment tuples, aggregating the cyclic harmonic comparison and joining the existing finite Gowers bound remain, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','Each vertex uses the actual signed difference sum over its subset of Fin d. Its bound follows from Fin coordinate bounds and subset cardinality at most d.','The scale inequality uses the exact natural floor division q/(J*a), with J positive and q nonzero. No divisibility or discarded rounding error is assumed.','The complete product includes every subset vertex and applies the existing 4H/q bound with H=d*a*floor(q/(J*a)). The final constant is 4d/J, not exponential in the number of vertices.','The statement is uniform in fixed increment tuples; averaging these tuples and joining the Gowers bound remain subsequent work. Three new theorems are individually kernel audited.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
