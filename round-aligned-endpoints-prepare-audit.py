from pathlib import Path
import re
p='round-aligned-endpoints'
s=Path('round-cell-partition-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-cell-partition'",f"PREFIX = '{p}'").replace("OLD = 'round-cell-mass-aggregation'","OLD = 'round-cell-partition'")
counts={'1037':'1039','1039':'1041','1021':'1023','1030':'1032','4895':'4901'}
s=re.sub(r'\b(?:1037|1039|1021|1030|4895)\b',lambda m:counts[m[0]],s)
s=s.replace('len(set(names)) == 5','len(set(names)) == 6').replace('len(names) == 5','len(names) == 6').replace('== 5\n','== 6\n').replace("'theorem_count': 5","'theorem_count': 6")
s=s.replace('new_theorems=5','new_theorems=6').replace('new_axiom_reports=5','new_axiom_reports=6').replace('new_theorem_count=5','new_theorem_count=6').replace('new_selected_report_count=5','new_selected_report_count=6')
modules=['Hindman168/AlignedInteriorEndpoints.lean','Hindman168/AlignedInteriorMassBound.lean']
components=['Explicit aligned endpoints (floor(A/R)+1)R and floor(B/R)R lie within R of the original endpoints. They are ordered if B-A is at least 2R. The deleted set lies in the two width-R end intervals and has at most 2R integer points, including when the interior is empty.','For positive X and the original positive harmonicNormalizer, integerMass at any y at least X is at most 1/(X*harmonicNormalizer). The actual mass deleted from the original window by the aligned interior is therefore at most 2R/(X*harmonicNormalizer).']
remaining='The aligned interior now has explicit endpoints, an exact at-most-2R deleted point bound and original integerMass loss at most 2R/(X*harmonicNormalizer). Endpoint-loss convergence along master parameters, admissible-residue restriction, normalized cell probabilities and wrapping errors still require assembly, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','Endpoint bounds follow from Euclidean division for arbitrary signed A and B, with R strictly positive. Ordering is claimed only with the explicit length condition B-A >= 2R.','The left endpoint advances to the next multiple even if A is already aligned. This may delete one full cell, and the proved bound is 2R rather than a strict 2R bound.','The deleted-set inclusion and cardinal bound do not assume a nonempty aligned interior or ordered endpoints. Overlapping endpoint strips are handled by the union cardinal inequality.','The mass bound uses the actual integerMass, its original coprimality filter and its original harmonicNormalizer. Positive X and normalizer are explicit, and no zero-normalizer stage is silently replaced.','Six theorems are individually kernel audited. The finite quantitative loss has been proved; its limiting convergence and the later global probability assembly remain open.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
