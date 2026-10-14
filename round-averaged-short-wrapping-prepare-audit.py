from pathlib import Path
import re
p='round-averaged-short-wrapping'
s=Path('round-short-cube-wrapping-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-short-cube-wrapping'",f"PREFIX = '{p}'").replace("OLD = 'round-cyclic-wrap-bound'","OLD = 'round-short-cube-wrapping'")
counts={'1051':'1052','1052':'1054','1034':'1036','1043':'1045','4928':'4932'}
s=re.sub(r'\b(?:1051|1052|1034|1043|4928)\b',lambda m:counts[m[0]],s)
s=s.replace('len(set(names)) == 3','len(set(names)) == 4').replace('len(names) == 3','len(names) == 4').replace('== 3\n','== 4\n').replace("'theorem_count': 3","'theorem_count': 4")
s=s.replace('new_theorems=3','new_theorems=4').replace('new_axiom_reports=3','new_axiom_reports=4').replace('new_theorem_count=3','new_theorem_count=4').replace('new_selected_report_count=3','new_selected_report_count=4').replace('new_module_count=1','new_module_count=2')
modules=['Hindman168/HaarMeanTestError.lean','Hindman168/AveragedShortCubeWrapping.lean']
components=['Finite Haar means preserve pointwise comparison errors on nonempty finite types. Exact subtraction and averaging identities give the short-cube wrapping bound after averaging both increment tuples.','The root-first cyclic and integer short-cube averages differ by at most 4d/J even after averaging over any nonnegative sum-one cell probabilities. The short interval is explicitly nonempty, and no tuple-count or cell-count factor appears.']
remaining='The short-cube wrapping bound 4d/J now holds after both increment averages and arbitrary cell-probability weighting in root-first order. Joining this with the original harmonic uniformization and the existing finite Gowers bound remains, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','Subtraction of finite Haar means is exact. The comparison lemma requires a nonempty finite type before using the absolute mean bound.','The short-cube theorem assumes positive floor(q/(J*a)), establishing nonempty increment types before both averaging steps. The root mean is reordered by an already proved finite triple-mean identity.','The weighted theorem assumes precisely nonnegative cell weights with sum one and invokes the proved averaging error, preserving the constant 4d/J independently of the number of cells.','The theorem permits different cell indices, residues and integer test functions for each cell. It does not assume a Gowers conclusion or an inverse correlator. Four new theorems are individually kernel audited.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
