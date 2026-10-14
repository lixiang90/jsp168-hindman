from pathlib import Path
import re
p='round-cyclic-wrap-bound'
s=Path('round-cyclic-cell-coordinates-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-cyclic-cell-coordinates'",f"PREFIX = '{p}'").replace("OLD = 'round-interior-renormalization'","OLD = 'round-cyclic-cell-coordinates'")
counts={'1048':'1049','1049':'1051','1031':'1033','1040':'1042','4921':'4925'}
s=re.sub(r'\b(?:1048|1049|1031|1040|4921)\b',lambda m:counts[m[0]],s)
s=s.replace('new_module_count=1','new_module_count=2')
modules=['Hindman168/CyclicCellInterior.lean','Hindman168/CyclicWrapTestError.lean']
components=['A finite family of signed shifts bounded in absolute value by H has identical integer and cyclic affine vertex products at roots with H <= z.val and z.val+H < q. The number of remaining ZMod q roots is at most 2H, including large margins.','Two unit-bounded cyclic tests agreeing on the interior differ in Haar mean by at most 4H/q. Consequently the actual affine cyclic vertex-product mean and the original integer-shift vertex-product mean differ by at most 4H/q, without a factor for the number of vertices.']
remaining='Quantitative cyclic wrapping error is now bounded by 4H/q for actual finite vertex products with signed shifts bounded by H. Instantiation for the original short-cube shifts, aggregation of the cyclic harmonic comparison and full short-cube transfer remain, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','Interior product agreement is proved factor by factor using the actual signed no-wrap coordinate equality. The finite set of shifts is arbitrary, so all cube vertices can be included simultaneously.','The boundary count maps actual ZMod q residues injectively to natural values. For H<=q it uses the union of two width-H intervals; for H>q it uses the total group size. No small-margin assumption is hidden.','The mean error bounds the pointwise difference by two on bad roots and zero on good roots, then divides the actual finite sum by q.','The product specialization derives absolute unit bounds from the bounds on the original integer function. Four new theorems are individually kernel audited; actual short-cube instantiation and inverse inputs remain incomplete.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
