from pathlib import Path
import re

source = Path('round-alternating-indices-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-alternating-indices'", "PREFIX = 'round-native-selected-models'")
source = source.replace("OLD = 'round-indexed-energy'", "OLD = 'round-alternating-indices'")
counts = {'963':'965','965':'967','947':'949','956':'958','4657':'4661','12':'4'}
source = re.sub(r'\b(?:963|965|947|956|4657|12)\b', lambda m: counts[m[0]], source)
source = source.replace('new_definitions=3', 'new_definitions=0')
source = source.replace('new_theorems=9', 'new_theorems=4').replace('new_theorem_count=9', 'new_theorem_count=4')
source = source.replace("== 9\n    root", "== 4\n    root").replace("'theorem_count': 9", "'theorem_count': 4")
modules = ['Hindman168/NativeSelectedModels.lean', 'Hindman168/NativeVaryingGapCommon.lean']
components = [
    'For original nonnegative probability masses, every support-wise [0,1] bounded Hilbert family has completed Hilbert norm at most one, with the estimate proved using its actual finite-mass L2 norm.',
    'The alternating Ramsey theorem is instantiated with actual native nilsequence closed subspaces and actual original-law Hilbert images. A master bound is fixed before the masses, parameter family, gap maps, ultrafilter and target families. For each selected block and label one actual native [0,1]-valued coarse model is chosen before every earlier padding index, and that same model satisfies all admissible fine residual bounds 2 epsilon.',
    'Finite native representations with distinct gap maps admit one actual common native product space and one common global observable and Lipschitz bound. Each represented function retains its own original interval partition. Empty families are covered by the actual trivial native nilmanifold.'
]
remaining = ('Native original-law selected models are now constructed with a master bound fixed before all data, exact coarse approximation and the same model valid for every admissible earlier padding. Finite representations on varying gap partitions have common native space and bounds. Next assemble simultaneous finite selected-model choices with common bounds and instantiate master gap maps and actual block laws. Calibration/Alignment, subgroup inverse inputs, actual coloring/arithmetic extraction, ordered positive rapidly separated monochromatic witnesses and required quantitative estimates remain. Original StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start = source.index('MODULES = ')
end = source.index('\n\ndef declarations', start)
source = source[:start] + 'MODULES = ' + repr(modules) + '\nCOMPONENTS = ' + repr(components) + '\nREMAINING = ' + repr(remaining) + '\n' + source[end:]
review = [
    'PROGRESS. Previous audit rechecked before edits and all 965 baseline hashes checked at registration. Prior proof sources, original targets, dependency pins and attribution remain unchanged.',
    'The actual native selected-model theorem has quantifier order: exists master N, then arbitrary master family, probability masses, ultrafilter, monotone-divisibility gap data and targets, then selected alternating indices, then one representative for each T,b,a, then every admissible earlier padding v. In particular the model cannot change with v.',
    'Projection energies use the actual nativeNilHilbertSubspace and hilbertFamilyToCompletion for the original mass at the selected principal pivot. Their [0,1] energy bounds are discharged using weighted L2 norm bounds, rather than supplied as independent hypotheses.',
    'Native clipped density produces the actual coarse representative. Refinement inclusion follows from the explicit divisibility assumption and padding monotonicity. Ramsey provides the energy gap, so the fine residual estimate no longer has an unproved energy-gap premise.',
    'Normalization and nonnegativity are explicit all-stage assumptions. Instantiation with concrete master block laws, including any initial-stage handling, is still required. No unproved concrete-law normalization is hidden in the theorem.',
    'Common-space induction now allows a different gap map at each finite label. Product embeddings preserve the same function and its own partition. Bounds are finite sums chosen after the family, uniform over labels, stages, pieces and quotient points, not claimed to be external quantitative complexity estimates.',
    'Four new theorems are registered individually for kernel axiom reports. Simultaneous finite choices still need assembly; Calibration/Alignment and the final target remain unproved.'
]
start = source.index('        application_review=[')
end = source.index('], new_modules=MODULES', start) + 1
source = source[:start] + '        application_review=' + repr(review) + source[end:]
Path('round-native-selected-models-audit.py').write_text(source, encoding='utf-8')
print('Prepared two-module audit: four theorems.')
