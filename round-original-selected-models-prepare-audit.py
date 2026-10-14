from pathlib import Path
import re
source = Path('round-master-probability-laws-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-master-probability-laws'", "PREFIX = 'round-original-selected-models'").replace("OLD = 'round-native-selected-models'", "OLD = 'round-master-probability-laws'")
counts = {'967':'970','970':'974','952':'956','961':'965','4674':'4686','13':'12'}
source = re.sub(r'\b(?:967|970|952|961|4674|13)\b', lambda m: counts[m[0]], source)
source = source.replace('new_definitions=3','new_definitions=2').replace('new_instances=1','new_instances=0')
source = source.replace('new_theorems=9','new_theorems=10').replace('new_theorem_count=9','new_theorem_count=10')
source = source.replace('== 9\n    root','== 10\n    root').replace("'theorem_count': 9","'theorem_count': 10").replace('new_module_count=3','new_module_count=4')
source = source.replace('    return {p: old.declarations(p) for p in MODULES}', '''    return {p: re.findall(r'^\\s*(?:noncomputable\\s+)?(theorem|lemma|def|abbrev|instance)\\s+([A-Za-z][A-Za-z0-9_\\.]*)', old.lean_code(read(p)), re.M) for p in MODULES}''')
modules = ['Hindman168/NativeSubprobApproximation.lean','Hindman168/NativeSubprobSelectedModels.lean','Hindman168/OriginalMasterSelectedModels.lean','Hindman168/MasterGapIndex.lean']
components = [
 'Native clipped approximation and all-padding selected models now hold for every original nonnegative law of total mass at most one. All projection and distance calculations retain the original Hilbert spaces.',
 'Actual original master pivot masses are substituted in selected-model selection, removing all-stage probability normalization and nonnegativity premises from its conclusion interface. The master Ramsey bound is fixed before the master family, ultrafilter, gap maps and target families.',
 'The canonical finite master gap map is monotone everywhere and exactly equal to the original index within range. Its gap divisibility is proved directly from MasterParameterConditions, preparing the concrete finite-master instantiation.'
]
remaining = ('Native subprobability clipped approximation and selected-model selection are proved, and actual original master masses are directly substituted without modifying any initial stage. A canonical finite master gap map has exact within-range values and proved divisibility. Next combine this map with the selected-index bound, make simultaneous finite model choices and common native representation bounds, then proceed to Calibration/Alignment and subgroup inverse inputs. Actual coloring/arithmetic extraction, ordered positive rapidly separated monochromatic witnesses and required quantitative estimates remain. Original StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start=source.index('MODULES = '); end=source.index('\n\ndef declarations',start)
source=source[:start]+'MODULES = '+repr(modules)+'\nCOMPONENTS = '+repr(components)+'\nREMAINING = '+repr(remaining)+'\n'+source[end:]
review=[
 'PROGRESS. Previous audit rechecked before edits. All 970 retained hashes checked at registration. Original proof sources, statement, mass definitions and dependency pins remain unchanged.',
 'Subprobability generalization changes only the total-mass hypothesis from equality one to at most one. It uses the previously checked subprobability clipping family and weighted distance contraction, including zero-mass stages.',
 'The native subspace is the same actual nativeNilHilbertSubspace as before. Density, orthogonality and product representations are unchanged; no abstract substitute Hilbert space or extra approximation hypothesis is introduced.',
 'Selected models are chosen per T,b,a before all admissible earlier padding indices v. The same representative satisfies every fine residual bound. Ramsey supplies the energy gap for actual native projections.',
 'OriginalMasterSelectedModels substitutes integerMass(F.cutoff w i,primorial w) at every original stage. Unconditional nonnegativity and total<=1 discharge the law assumptions. No truncation, rescaling, totalization, shift or replacement law is used.',
 'The master bound is chosen before F, U, gap maps and all target families. Target [0,1] bounds are still explicit. The finite gap map clamps out-of-range indices only to give a total function; exact equality is proved for all within-range indices. Full selected-index instantiation remains next.',
 'The declaration parser includes the new abbrev originalPivotMass in addition to all definitions and theorems. Ten theorems and two definitions/abbreviations receive individual kernel axiom reports. No completed main target is claimed.'
]
start=source.index('        application_review=['); end=source.index('], new_modules=MODULES',start)+1
source=source[:start]+'        application_review='+repr(review)+source[end:]
Path('round-original-selected-models-audit.py').write_text(source,encoding='utf-8')
print('Prepared four-module audit: ten theorems, two definitions/abbreviations, twelve reports.')
