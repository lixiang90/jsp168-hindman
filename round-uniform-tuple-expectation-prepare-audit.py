from pathlib import Path
import re
source=Path('round-uniform-image-density-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-uniform-image-density'", "PREFIX = 'round-uniform-tuple-expectation'").replace("OLD = 'round-haar-difference-density'", "OLD = 'round-uniform-image-density'")
counts={'1016':'1019','1019':'1022','1001':'1004','1010':'1013','4838':'4846'}
source=re.sub(r'\b(?:1016|1019|1001|1010|4838)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=8','new_theorems=7').replace('new_theorem_count=8','new_theorem_count=7')
source=source.replace('== 8\n    root','== 7\n    root').replace("'theorem_count': 8","'theorem_count': 7")
source=source.replace('len(set(names)) == 9','len(set(names)) == 8').replace('len(names) == 9','len(names) == 8').replace('new_axiom_reports=9','new_axiom_reports=8').replace('new_selected_report_count=9','new_selected_report_count=8')
modules=['Hindman168/UniformTupleExpectation.lean','Hindman168/UniformShortCubeBound.lean','Hindman168/MultipleCyclicIntervalEmbedding.lean']
components=[
 'The product of actual image Haar densities gives exactly the uniform source-tuple expectation under coordinatewise injective maps. The identity is also proved for two independent tuples, including zero coordinates.',
 'The weighted short-increment cube bound is now stated directly for uniform interval tuples, with increments e(v)-e(u), and gives constant (2J)^d times the original subgroup Gowers value in dimension 2^d.',
 'The explicit map u -> q*u from Fin n onto the q-multiple subgroup of ZMod(q*n) is proved injective for q>0 and surjective for q,n>0. Its subgroup cardinality is exactly n; restriction to any interval of length at most n remains injective.'
]
remaining='Uniform source tuple and pair expectations are now exactly linked to the density expressions, giving a direct weighted uniform-short-cube bound. The explicit q-multiple cyclic subgroup embedding and cardinality are proved. Instantiation with the master-scale quotient parameters, the harmonic-to-periodized Haar comparison, Bessel input, cyclic-to-interval transfer and inverse correlator existence remain. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 1019 baseline hashes verified at registration. Prior proof sources, original target, laws and pins remain intact.',
 'The tuple expectation identity is proved by induction on the original coordinate count using exact Fin.cons Haar decomposition and the one-coordinate uniform image expectation. The empty tuple case uses the unique function from Fin 0.',
 'The two-tuple identity applies the tuple pushforward twice and retains the same coordinatewise maps and their original uniform source laws.',
 'The direct short-cube theorem preserves v-u ordering and every original cell probability. It has no auxiliary density variables in its final expression; its source interval length is floor(card(Q)/J).',
 'The cyclic embedding takes values in the original multipleAddSubgroup and carries its explicit range witness. Injectivity uses q*u<q*n and actual ZMod residue values, followed by cancellation of positive q.',
 'Surjectivity uses the representative z.val modulo n, the Euclidean remainder identity and the vanishing of q*n in ZMod(q*n). Both q and n are positive before using the positive-modulus cast identity.',
 'The subgroup cardinality is obtained from this actual bijection, and the short-interval restriction is injective by composing with Fin.castLE.',
 'Seven theorems and one definition are individually kernel audited. Master-scale parameter instantiation, harmonic periodization errors, Bessel and inverse inputs, and the final target remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-uniform-tuple-expectation-audit.py').write_text(source,encoding='utf-8')
print('Prepared three-module audit: seven theorems, one definition.')
