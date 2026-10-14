from pathlib import Path
import re
source=Path('round-selected-chain-indices-audit.py').read_text(encoding='utf-8')
source=source.replace("PREFIX = 'round-selected-chain-indices'","PREFIX = 'round-native-correlation'").replace("OLD = 'round-concrete-master-selection'","OLD = 'round-selected-chain-indices'")
counts={'976':'978','978':'981','960':'963','969':'972','4694':'4702'}
source=re.sub(r'\b(?:976|978|960|969|4694)\b',lambda m:counts[m[0]],source)
source=source.replace('new_theorems=5','new_theorems=7').replace('new_theorem_count=5','new_theorem_count=7')
source=source.replace('== 5\n    root','== 7\n    root').replace("'theorem_count': 5","'theorem_count': 7")
source=source.replace('len(set(names)) == 6','len(set(names)) == 8').replace('len(names) == 6','len(names) == 8').replace('new_axiom_reports=6','new_axiom_reports=8').replace('new_selected_report_count=6','new_selected_report_count=8').replace('new_module_count=2','new_module_count=3')
modules=['Hindman168/NativeStageRestriction.lean','Hindman168/NativeProjectionCorrelation.lean','Hindman168/NativeUltrafilterRestriction.lean']
components=[
 'Any actual native piecewise representation may be restricted to an arbitrary set of stages and set to zero outside it, preserving its original native space, lattice, step, partition and uniform observable/Lipschitz bounds.',
 'Correlation with a unit-norm vector in an actual closed subspace is bounded by the projection norm. Applied to actual native representing families and original subprobability masses, this bounds their exact weighted Hilbert correlation. An eventual positive original correlation with a tending-to-zero error forces the corresponding positive native projection lower bound.',
 'Actual stage restriction of a bounded correlator supplies a bounded original-law Hilbert family. On an ultrafilter-large stage set its completed vector is proved identical to the original vector by the zero-distance characterization, and its native representation is retained.'
]
remaining=('The correlation-to-projection conclusion and restriction to ultrafilter-large stage sets are now proved on actual original-law native representations. The existence of the inverse correlator is not assumed away or proved by these statements. Next establish finite subgroup Gowers inputs, cyclic-to-interval transfer and weighted cell assembly needed to derive positive correlations, alongside coloring-derived dense targets. Calibration/Alignment and final arithmetic extraction of ordered positive rapidly separated monochromatic witnesses remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start=source.index('MODULES = ');end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked and all 978 baseline hashes verified before registration. Prior proofs, original target, law definitions and source/dependency pins remain unchanged.',
 'Reviewed against the final paragraphs of the subgroup-inverse lemma in fixed 05_prediction.tex. This increment proves the analytic implication from an existing native correlator to a positive projection, not the GTZ inverse theorem or the Bessel input.',
 'Stage restriction constructs an actual observable equal to the original observable or the zero continuous map, with unchanged translations, basepoints, partition and native lattice. Nonnegative B and Lipschitz weakening justify the zero branch uniformly.',
 'Orthogonality identifies correlation with correlation against the projection; Cauchy-Schwarz and the actual original weighted norm bound then control its absolute value. The correlator is allowed to take both signs, so the hypothesis is abs(v)<=1, not v in [0,1].',
 'Eventual correlation lower bounds with an explicit error tending to zero are transferred using the actual ultrafilter limit of weighted expectations. No exchange of limits or unproved convergence is inserted.',
 'The restricted family is bounded under total<=1, including zero-mass stages. On the ultrafilter-large set it equals the original coordinate family exactly, so the completed equality follows from the verified zero-distance criterion.',
 'Seven theorems and one definition are individually kernel audited. Full inverse correlator existence, finite subgroup estimates, coloring-derived targets, Calibration/Alignment and final combinatorial conclusion remain.'
]
start=source.index('        application_review=[');end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-native-correlation-audit.py').write_text(source,encoding='utf-8')
print('Prepared three-module audit: seven theorems, one definition.')
