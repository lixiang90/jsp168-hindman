from pathlib import Path
import re
source=Path('round-original-selected-models-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-original-selected-models'", "PREFIX = 'round-concrete-master-selection'").replace("OLD = 'round-master-probability-laws'", "OLD = 'round-original-selected-models'")
counts={'970':'974','974':'976','956':'958','965':'967','4686':'4688','12':'2'}
source=re.sub(r'\b(?:970|974|956|965|4686|12)\b',lambda m:counts[m[0]],source)
source=source.replace('new_definitions=2','new_definitions=0').replace('new_theorems=10','new_theorems=2').replace('new_theorem_count=10','new_theorem_count=2')
source=source.replace('== 10\n    root','== 2\n    root').replace("'theorem_count': 10","'theorem_count': 2").replace('new_module_count=4','new_module_count=2')
modules=['Hindman168/ConcreteMasterSelectedModels.lean','Hindman168/FiniteMasterSelectedModels.lean']
components=[
 'Concrete master selection now discharges the abstract gap-divisibility premise from MasterParameterConditions. Every sufficiently large positive master size supplies selected indices in its original range, and the canonical gap map is proved exactly equal to every selected original index at every stage.',
 'All subsets of the finite principal index type, all selected pivots and all finite labels now have simultaneously chosen actual [0,1]-valued native models. Each model retains its coarse epsilon approximation and every admissible earlier-padding 2 epsilon residual bound.',
 'The finite selected-model family has one actual native nilmanifold, one global observable bound and one global Lipschitz constant. Exact original piecewise orbit representations are supplied for every tail/pivot/label, each using its own selected coarse gap, with constants uniform over all stages and pieces.'
]
remaining=('Concrete master conditions and the selected-index range now discharge gap divisibility and ensure original interval indices. Simultaneous models for every finite principal tail, pivot and label have coarse/fine projection estimates and one common native manifold with global observable/Lipschitz bounds. Targets remain arbitrary support-wise [0,1] bounded families in the actual original master Hilbert laws; actual coloring-derived dense targets still need instantiation. Next connect selected finite tails to chain blocks and proceed through Calibration/Alignment, subgroup inverse inputs, actual coloring/arithmetic extraction, ordered positive rapidly separated monochromatic witnesses and required quantitative estimates. StrongConjecture remains unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 974 retained source/config hashes verified at registration. Original targets, prior proofs, laws and dependency pins remain unchanged.',
 'Concrete selection uses any positive master size M at least the uniform Ramsey bound. MasterParameterConditions supplies all gap-divisibility premises. Every selected position is proved less than M, and the canonical map returns exactly that index; no out-of-range clamping affects any selected interval.',
 'The Ramsey bound precedes the master family, parameters, ultrafilter and target data. The law remains integerMass(F.cutoff w i,primorial w) at each original stage.',
 'Finite tails are indexed by Finset(Fin n), then mapped to the principal set. The finite family includes every such tail, selected pivot and label. Classical choice chooses one model for each triple before the earlier-padding quantifier, preserving the same model for all admissible chain comparisons.',
 'Common-space and bound assembly uses the actual finite product construction for varying gaps. The returned observables, translations and basepoints have an exact pointwise piecewise representation for each model. One B and one Lip precede all finite labels and all stages, pieces and points.',
 'Constants depend on the chosen finite family. No quantitative bound uniform over every possible master family or target is claimed. The target family is still an explicit support-wise [0,1] input, so this is not yet the full coloring-derived prediction theorem.',
 'Both new theorems are individually kernel audited. Chain-block instantiation, Calibration/Alignment and final arithmetic extraction remain; no completed target or unavoidable blocker is claimed.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-concrete-master-selection-audit.py').write_text(source,encoding='utf-8')
print('Prepared two-module audit: two aggregate theorems.')
