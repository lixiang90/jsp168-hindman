from pathlib import Path
import re
p='round-interior-mass-limit'
s=Path('round-master-endpoint-loss-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-master-endpoint-loss'",f"PREFIX = '{p}'").replace("OLD = 'round-aligned-endpoints'","OLD = 'round-master-endpoint-loss'")
counts={'1041':'1043','1043':'1045','1025':'1027','1034':'1036','4905':'4910'}
s=re.sub(r'\b(?:1041|1043|1025|1034|4905)\b',lambda m:counts[m[0]],s)
s=s.replace('len(set(names)) == 4','len(set(names)) == 5').replace('len(names) == 4','len(names) == 5').replace('== 4\n','== 5\n').replace("'theorem_count': 4","'theorem_count': 5")
s=s.replace('new_theorems=4','new_theorems=5').replace('new_axiom_reports=4','new_axiom_reports=5').replace('new_theorem_count=4','new_theorem_count=5').replace('new_selected_report_count=4','new_selected_report_count=5')
modules=['Hindman168/AlignedInteriorMassSplit.lean','Hindman168/MasterAlignedInteriorMass.lean']
components=['The original integerMass support lies inside Ico X X^2, so its sum on that window is its exact total. The mass of the aligned interior plus the deleted endpoint mass equals that original total, even at zero-normalizer stages.','The aligned interior mass tends to one along the actual master scales and is eventually strictly positive, using the proved endpoint-loss convergence and eventual positivity of the original normalizer.']
remaining='The actual aligned interior mass now tends to one and is eventually positive, with an exact decomposition retaining all zero-normalizer stages. Admissible-residue restriction, assembly and renormalization of cell probabilities, and wrapping errors remain to connect, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous audit rechecked and all baseline proof hashes preserved.','Support containment is proved from the actual mapDomain and harmonicWindow support, preserving the original coprimality filter.','The interior is a subset of the original window from the proved endpoint bounds, even when empty. The sum split is a disjoint finite-set difference identity.','The finite split equals the original total, not an assumed constant one; it is valid even when the normalizer vanishes.','The limiting proof replaces the total by one only on the proved eventual positive-normalizer set, then uses the actual endpoint-loss convergence. Strict positivity of the interior mass follows from its limit one.','Five new theorems are individually kernel audited. No global normalized cell law or inverse correlator is assumed; these remain to construct.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
