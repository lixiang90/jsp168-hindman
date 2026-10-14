from pathlib import Path
import re
source=Path('round-native-correlation-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-native-correlation'","PREFIX = 'round-coprime-subgroup-sum'").replace("OLD = 'round-selected-chain-indices'","OLD = 'round-native-correlation'")
counts={'978':'981','981':'983','963':'965','972':'974','4702':'4709'}
source=re.sub(r'\b(?:978|981|963|972|4702)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=7','new_theorems=6').replace('new_theorem_count=7','new_theorem_count=6')
source=source.replace('== 7\n    root','== 6\n    root').replace("'theorem_count': 7","'theorem_count': 6")
source=source.replace('len(set(names)) == 8','len(set(names)) == 7').replace('len(names) == 8','len(names) == 7').replace('new_axiom_reports=8','new_axiom_reports=7').replace('new_selected_report_count=8','new_selected_report_count=7').replace('new_module_count=3','new_module_count=2')
modules=['Hindman168/CoprimeMultipleSubgroups.lean','Hindman168/WeightedSubgroupCombination.lean']
components=[
 'The actual multiple subgroup qG is defined as the range of the natural multiplication homomorphism. Integer Bezout coefficients give an explicit decomposition x=a*y+b*z for coprime a,b in every additive abelian group, proving aG+bG=G and its actual ZMod cyclic specialization.',
 'For subgroup statistics bounded above by one and nonnegative at the full group, the original finite probability-weighted average over pairwise multiple-subgroup sums is at most the full-group statistic plus the exact weighted probability of noncoprime pairs. No bound depends on the number of indices.'
]
remaining=('The exact Bezout subgroup-sum identity and probability-weighted noncoprime-pair error bound are now proved. These support the combining-subgroups paragraph of the inverse argument but do not establish Gowers norm properties or the Bessel inverse input. Next construct the actual subgroup cube norms and their finite-system estimates, cyclic-to-interval transfer, weighted cell assembly and inverse correlators. Coloring-derived dense targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous round rechecked before edits. All 981 retained hashes verified at registration; original targets, prior proofs, laws, pins and attribution remain unchanged.',
 'Follows the combining-subgroups paragraph of fixed 05_prediction.tex. The subgroup is the actual image of multiplication by q, not an abstract subgroup assumed to satisfy a sum identity.',
 'The decomposition uses Nat.gcdA and Nat.gcdB as integer scalar coefficients and the exact Bezout identity. Negative coefficients are legitimate in the additive group. The theorem covers cyclic groups directly and does not assume a field or invertibility of either coefficient separately.',
 'The subgroup sum is the lattice join of actual additive subgroups; explicit summands prove every group element lies in the join. This corresponds to the paper subgroup sum, not multiplication of elements in a quotient.',
 'The weighted error estimate assumes nonnegative finite weights summing to one and retains their product weights. On coprime pairs the actual subgroup join is top; on the complement a bounded statistic costs at most one. Summing the constant term uses exact normalization.',
 'The statistic is deliberately an explicit arbitrary subgroup function with upper bound one and nonnegative full-group value. This theorem does not claim Gowers norms or a Bessel modulus have already been constructed. Their properties remain a separate obligation.',
 'One definition and six theorems are individually registered for kernel axiom audit. No completed inverse theorem or main target is claimed.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-coprime-subgroup-sum-audit.py').write_text(source,encoding='utf-8')
print('Prepared two-module audit: six theorems, one definition.')
