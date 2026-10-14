from pathlib import Path
import re
p='round-cyclic-cell-coordinates'
s=Path('round-interior-renormalization-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-interior-renormalization'",f"PREFIX = '{p}'").replace("OLD = 'round-admissible-cell-probabilities'","OLD = 'round-interior-renormalization'")
counts={'1046':'1048','1048':'1049','1030':'1031','1039':'1040','4917':'4921'}
s=re.sub(r'\b(?:1046|1048|1030|1039|4917)\b',lambda m:counts[m[0]],s)
s=s.replace('len(set(names)) == 3','len(set(names)) == 4').replace('len(names) == 3','len(names) == 4').replace('== 3\n','== 4\n').replace("'theorem_count': 3","'theorem_count': 4")
s=s.replace('new_theorems=3','new_theorems=4').replace('new_axiom_reports=3','new_axiom_reports=4').replace('new_theorem_count=3','new_theorem_count=4').replace('new_selected_report_count=3','new_selected_report_count=4').replace('new_module_count=2','new_module_count=1')
modules=['Hindman168/CyclicCellCoordinates.lean']
components=['The uniform Fin q coordinate average on an actual complete residue cell is exactly the Haar average on ZMod q under the affine representative kMq+r+M*z.val. The original integerMass conditional error therefore compares directly with this cyclic Haar mean.','For any signed integer shift h, if the shifted affine representative remains in the same half-open cell, its value equals the affine representative of z+h in ZMod q. The required no-wrap coordinate bounds are derived from actual cell containment and the residue bound.']
remaining='Actual complete cells now have exact cyclic Haar coordinates and no-wrap translation compatibility, with the original conditional harmonic error expressed on ZMod q. Aggregating the cyclic comparison, quantitative wrapping errors and full short-cube transfer remain, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','The cyclic group is the actual ZMod q with q nonzero. The Fin q uniform mean and ZMod q Haar mean agree by the library representation, without changing cardinalities or normalizations.','The modular addition value theorem requires explicit lower and strict upper coordinate bounds. It applies to signed shifts, so negative increments are retained.','For the affine original cell, these coordinate bounds are derived from actual shifted-integer containment, positive M and r<M. No wrap is silently ignored.','The final theorem retains the actual integerMass cell, coprimality filter, positive original normalizer and positive left endpoint. Four theorems are individually kernel audited; wrapping and inverse inputs remain unfinished.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
