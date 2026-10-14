from pathlib import Path
import re
p='round-cell-partition'
s=Path('round-cell-mass-aggregation-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-cell-mass-aggregation'",f"PREFIX = '{p}'").replace("OLD = 'round-integer-cell-mass'","OLD = 'round-cell-mass-aggregation'")
counts={'1035':'1037','1037':'1039','1019':'1021','1028':'1030','4890':'4895'}
s=re.sub(r'\b(?:1035|1037|1019|1028|4890)\b',lambda m:counts[m[0]],s)
s=s.replace('len(set(names)) == 3','len(set(names)) == 5').replace('len(names) == 3','len(names) == 5').replace('== 3\n','== 5\n').replace("'theorem_count': 3","'theorem_count': 5")
s=s.replace('new_theorems=3','new_theorems=5').replace('new_axiom_reports=3','new_axiom_reports=5').replace('new_theorem_count=3','new_theorem_count=5').replace('new_selected_report_count=3','new_selected_report_count=5')
modules=['Hindman168/CompleteResidueCellPartition.lean','Hindman168/AlignedIntervalResiduePartition.lean']
components=['Membership in an actual complete residue cell is equivalent to the existing intervalResiduePiece label. Distinct integer interval/residue labels give disjoint cells, and the sum over any finite union is exactly the sum of the cell sums.','For positive R and M, cells with interval indices in Ico a b and every residue in Fin M form an exact disjoint partition of Ico (aR) (bR). The original integer sum is exactly reindexed by these interval indices and residues, including empty intervals.']
remaining='The original intervalResiduePiece labels now give a proved exact disjoint partition and sum decomposition of aligned integer intervals. Selecting the aligned interior of the original harmonic window, deleting the partial endpoint pieces, restricting to admissible residues, assembling normalized cell probabilities and wrapping errors remain, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','Cell membership is identified with the existing quotient/remainder intervalResiduePiece; positivity of R is required for the Euclidean quotient bounds. No replacement partition is introduced.','Disjointness uses equality of the original labels and injectivity of the Fin residue cast.','Aligned coverage constructs the unique quotient interval and canonical nonnegative remainder modulo M. Both moduli are strictly positive; arbitrary signed endpoints and empty intervals are retained.','The finite sum decomposition is exact and uses the proved disjointness. This does not yet identify a specific interior of the harmonic window or bound its deleted endpoints. Five new theorems are individually kernel audited.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
