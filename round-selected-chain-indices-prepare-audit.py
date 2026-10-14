from pathlib import Path
import re
source=Path('round-concrete-master-selection-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-concrete-master-selection'","PREFIX = 'round-selected-chain-indices'").replace("OLD = 'round-original-selected-models'","OLD = 'round-concrete-master-selection'")
counts={'974':'976','976':'978','958':'960','967':'969','4688':'4694'}
source=re.sub(r'\b(?:974|976|958|967|4688)\b',lambda m:counts[m[0]],source)
source=source.replace('new_definitions=0','new_definitions=1').replace('new_theorems=2','new_theorems=5').replace('new_theorem_count=2','new_theorem_count=5')
source=source.replace('== 2\n    root','== 5\n    root').replace("'theorem_count': 2","'theorem_count': 5")
source=source.replace('len(set(names)) == 2','len(set(names)) == 6').replace('len(names) == 2','len(names) == 6').replace('new_axiom_reports=2','new_axiom_reports=6').replace('new_selected_report_count=2','new_selected_report_count=6')
modules=['Hindman168/SelectedChainIndices.lean','Hindman168/ChainMasterSelectedModels.lean']
components=[
 'Every actual Chain on the selected principal set has recovered finite pivot coordinates and exact finite tail coordinates. The first pivot coordinate is no greater than every later one, and every tail lies below the single padding immediately preceding that first pivot.',
 'The existing chain allocation theorem applies to the actual principal set, preserving prescribed block cardinalities and its true all-tails-before-all-pivots ordering.',
 'The full finite native model theorem now supplies all actual chains on the selected principal set with a common fine padding and projected residual at most 2 epsilon for every block and label. The same models and common native observable bounds were chosen before the chain, not separately for each chain.'
]
remaining=('Actual chains on selected principal indices are now connected to simultaneously selected native models, with exact finite tail/pivot coordinates, a common fine padding before the first pivot and blockwise 2 epsilon projected residuals. Common native manifold and uniform observable bounds are retained before all chain choices. Next connect coloring-derived dense target families and subgroup inverse inputs to this projection conclusion, then Calibration/Alignment and final arithmetic extraction of ordered positive rapidly separated monochromatic witnesses. Required quantitative estimates remain. Original StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before editing. All 976 baseline hashes checked at registration. Prior proofs, original target, original laws and pins remain intact.',
 'Chain is the existing structure with nonempty ordered tails, all tails before all pivots, and strictly increasing pivots. The proof uses these exact fields; it does not replace this by an ordered-block condition.',
 'principalTailPositions is the finite preimage inside Fin n. Its image is proved exactly the original tail whenever the tail lies in the principal set. Pivot coordinates are recovered by the actual injective principal embedding.',
 'For every nonempty chain the first pivot has the least recovered position. All chain tails precede that first pivot, and the alternating-order lemma places them below its padding. This is one padding for all chain blocks.',
 'The model theorem retains the original master masses, exact selected gap indices, simultaneous coarse models and the common native representation bound. The chain quantifier occurs after the model family: no new model can be selected depending on the chain.',
 'The fine bound is the previously proved all-padding estimate specialized using exact tail-image equalities and first-pivot order. The actual model is indexed by the recovered tail and pivot; the target is f(C.tail i,C.pivot i,a), expressed with its proved coordinate equality.',
 'Allocation of chains with prescribed block sizes follows from the existing allocation theorem and exact principal-set cardinality n. Subgroup inverse inputs, coloring-derived targets, Calibration/Alignment and final arithmetic extraction remain unproved.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-selected-chain-indices-audit.py').write_text(source,encoding='utf-8')
print('Prepared two-module audit: five theorems, one definition.')
