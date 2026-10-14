from pathlib import Path
import re
p='round-full-window-short-gowers'
s=Path('round-aligned-global-gowers-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-aligned-global-gowers'",f"PREFIX = '{p}'").replace("OLD = 'round-cell-disintegration'","OLD = 'round-aligned-global-gowers'")
counts={'1058':'1059','1059':'1061','1041':'1043','1050':'1052','4939':'4942'}
s=re.sub(r'\b(?:1058|1059|1041|1050|4939)\b',lambda m:counts[m[0]],s)
s=s.replace('len(set(names)) == 1','len(set(names)) == 3').replace('len(names) == 1','len(names) == 3').replace('== 1\n    root','== 3\n    root').replace("'theorem_count': 1","'theorem_count': 3")
s=s.replace('new_theorems=1','new_theorems=3').replace('new_axiom_reports=1','new_axiom_reports=3').replace('new_theorem_count=1','new_theorem_count=3').replace('new_selected_report_count=1','new_selected_report_count=3').replace('new_module_count=1','new_module_count=2')
modules=['Hindman168/FullWindowShortCubeBound.lean','Hindman168/MasterShortCubeRemainder.lean']
components=['The full original harmonic-window short-cube test is bounded by the actual-cell weighted Gowers quantity, 4d/J, R/X and twice the actual deleted mass. The transfer uses the proved finite probability renormalization estimate and a derived unit bound for the short-cube test.','At the original ordered master scales, R/X tends to zero and so does its sum with twice the actual aligned-endpoint deletion mass. Thus the full-window finite bound has a proved vanishing remainder separate from 4d/J.']
remaining='The full original-window short-cube bound and vanishing master remainder R/X plus twice the deleted mass are proved. Instantiating the complete bound with the actual master quotient and short-length geometry remains, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','The full-window theorem uses the actual integerMass and the exact same finite cell probabilities as the aligned theorem. The added term is twice the actual deleted mass, not an assumed small error.','The short-cube test is proved unit-bounded before applying finite retained-probability comparison. Positive original normalizer supplies total one and positive retained mass is explicit.','The master R/X limit is dominated by the already proved W(R+1)/X rate using primorial>=1, without an extra growth assumption.','The combined remainder limit adds R/X to twice the already proved actual endpoint mass loss. Zero-normalizer stages remain in the sequences.','Three new theorems are individually kernel audited. The fully instantiated master Gowers theorem and the Bessel/inverse inputs remain unfinished.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
