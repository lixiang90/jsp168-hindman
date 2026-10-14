from pathlib import Path
import re
p='round-integer-cell-mass'
s=Path('round-residue-cell-parametrization-audit.py').read_text(encoding='utf-8')
s=s.replace("PREFIX = 'round-residue-cell-parametrization'",f"PREFIX = '{p}'").replace("OLD = 'round-harmonic-cell-uniformity'","OLD = 'round-residue-cell-parametrization'")
counts={'1031':'1033','1033':'1035','1015':'1017','1024':'1026','4882':'4887'}
s=re.sub(r'\b(?:1031|1033|1015|1024|4882)\b',lambda m:counts[m[0]],s)
s=s.replace('len(set(names)) == 9','len(set(names)) == 5').replace('len(names) == 9','len(names) == 5').replace('== 8\n','== 5\n').replace("'theorem_count': 8","'theorem_count': 5")
s=s.replace('new_theorems=8','new_theorems=5').replace('new_definitions=1','new_definitions=0').replace('new_axiom_reports=9','new_axiom_reports=5').replace('new_theorem_count=8','new_theorem_count=5').replace('new_selected_report_count=9','new_selected_report_count=5')
modules=['Hindman168/CompleteResidueCellMass.lean','Hindman168/CompleteResidueCellMassError.lean']
components=['When W divides M, coprimality with W is constant on each residue class modulo M. On an actual complete cell inside the original harmonic window, integerMass sums equal the reciprocal coordinate sum divided by the original harmonicNormalizer for admissible residues, and zero otherwise.','For an admissible complete cell and positive original normalizer, the original integerMass conditional expectation equals the explicit coordinate harmonic ratio. Its discrepancy from the uniform Fin q mean is bounded by Mq/(kMq).']
remaining='The original integerMass complete-cell sum and conditional expectation are now connected to the explicit coordinates with the exact unit-residue filter. Global cell probabilities, deletion of partial endpoint cells, renormalization and wrapping errors still require assembly, followed by Bessel input, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
a=s.index('MODULES = ');b=s.index('\n\ndef declarations',a)
s=s[:a]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+s[b:]
review=['PROGRESS. Previous round rechecked before edits; all baseline source hashes verified at registration.','The original integerMass and harmonicWindow definitions are used directly. Coprimality is transported by the actual divisibility W | M and residue identity, via the Euclidean gcd recursion.','The sum formula includes both admissible and inadmissible residues, and is valid even for a zero normalizer. No probability law is replaced.','The conditional ratio theorem requires positivity of the original harmonicNormalizer before cancelling it. The error theorem additionally requires positive cell length and left endpoint.','All five new theorems are individually kernel checked. Global cell weights, endpoint deletion, wrapping and the deep inverse inputs remain open.']
a=s.index('        application_review=[');b=s.index('], new_modules=MODULES',a)+1
s=s[:a]+'        application_review='+repr(review)+s[b:]
Path(p+'-audit.py').write_text(s,encoding='utf-8')
