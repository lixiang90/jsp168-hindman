from pathlib import Path
import re
p='round-cell-disintegration'
s=Path('round-harmonic-short-gowers-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-harmonic-short-gowers'",f"PREFIX = '{p}'").replace("OLD = 'round-integer-short-gowers'","OLD = 'round-harmonic-short-gowers'")
counts={'1055':'1057','1057':'1058','1039':'1040','1048':'1049','4936':'4938'}
s=re.sub(r'\b(?:1055|1057|1039|1048|4936)\b',lambda m:counts[m[0]],s)
s=s.replace('new_module_count=2','new_module_count=1')
modules=['Hindman168/AlignedCellDisintegration.lean']
components=['Every admissible cell indexed by the actual aligned interval has strictly positive original integerMass, derived from global interval containment, positive X and the original positive normalizer.','The actual cell probability times its conditional test average sums exactly to the retained interval test divided by its retained mass. This disintegration identity uses the proved admissible-cell partition and cancels only proved nonzero cell masses.']
remaining='Exact disintegration now identifies the actual probability-weighted conditional cell tests with the normalized retained-interval test. Instantiating the finite cell index in the harmonic Gowers bound and applying master rate limits remains, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','Global aligned interval containment implies both endpoints of each indexed cell lie in the original harmonic window. Positive X implies the positive cell left endpoint needed by the previous mass theorem.','The disintegration formula uses actual integerMass, exact admissible residues and the actual retained interval denominator, with an arbitrary real test function.','Each cell denominator is cancelled only after its strict positivity has been proved. The total denominator is not cancelled, so the identity also covers empty retained intervals; treating the weights as probabilities still requires the previously proved positive retained mass.','The final equality is the exact admissible-cell sum identity divided by the unchanged total denominator. Two new theorems are individually kernel audited; the global Gowers specialization and inverse inputs remain open.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
