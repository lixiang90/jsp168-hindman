from pathlib import Path
import re
p='round-integer-short-gowers'
s=Path('round-averaged-short-wrapping-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-averaged-short-wrapping'",f"PREFIX = '{p}'").replace("OLD = 'round-short-cube-wrapping'","OLD = 'round-averaged-short-wrapping'")
counts={'1052':'1054','1054':'1055','1036':'1037','1045':'1046','4932':'4934'}
s=re.sub(r'\b(?:1052|1054|1036|1045|4932)\b',lambda m:counts[m[0]],s)
s=s.replace('len(set(names)) == 4','len(set(names)) == 2').replace('len(names) == 4','len(names) == 2').replace('== 4\n','== 2\n').replace("'theorem_count': 4","'theorem_count': 2")
s=s.replace('new_theorems=4','new_theorems=2').replace('new_axiom_reports=4','new_axiom_reports=2').replace('new_theorem_count=4','new_theorem_count=2').replace('new_selected_report_count=4','new_selected_report_count=2').replace('new_module_count=2','new_module_count=1')
modules=['Hindman168/IntegerShortCubeGowersBound.lean']
components=['The short increment lengths (a*n)/(J*a) and n/J are exactly equal for positive a. Integer difference sums cast to the cyclic group are exactly the subgroup cube vertices used by the existing Gowers bound.','The cell-probability-weighted integer short-cube root/increment average is bounded by (2J)^d times the original weighted subgroup Gowers value of order 2^d, plus the quantitative wrapping error 4d/J, on ZMod(a*n) with subgroup of multiples of a.']
remaining='The weighted integer short-cube average is now bounded directly by the finite subgroup Gowers quantity plus 4d/J. Aggregating original harmonic uniformization with this bound remains, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','Positive a justifies exact cancellation of a in the natural floor quotient. The short length n/J is explicitly positive before averaging.','The cyclic observable is the actual original integer function pulled back along the affine cell representative. Its unit bound follows directly from the original integer bound.','Integer casts of the signed subset sums are identified exactly with the existing cyclic subgroup vertices. The Gowers estimate and the previously proved wrapping estimate are then combined by the absolute-value triangle inequality.','The subgroup is the actual multiples-of-a subgroup in ZMod(a*n), and the Gowers order remains 2^d. No Bessel or inverse-theorem hypothesis is introduced. Two new theorems are individually kernel audited.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
lean=Path(modules[0]).read_text(encoding='utf-8')
Path(p+'-write.py').write_text('from pathlib import Path\nPath('+repr(modules[0])+').write_text('+repr(lean)+',encoding="utf-8")\n',encoding='utf-8')
