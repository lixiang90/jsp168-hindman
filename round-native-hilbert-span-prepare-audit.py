from pathlib import Path
import re

source = Path('round-product-nil-representation-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-product-nil-representation'", "PREFIX = 'round-native-hilbert-span'")
source = source.replace("OLD = 'round-piece-refinement-hilbert'", "OLD = 'round-native-product-data'")
counts = {'945':'958','951':'960','933':'942','942':'951','4570':'4635','25':'15','18':'11'}
source = re.sub(r'\b(?:945|951|933|942|4570|25|18)\b', lambda m: counts[m[0]], source)
source = source.replace('new_definitions=7', 'new_definitions=3').replace('new_instances=0', 'new_instances=1')
source = source.replace('new_module_count=6', 'new_module_count=2')
modules = ['Hindman168/NativeHilbertRepresentations.lean', 'Hindman168/NativeHilbertClippedApproximation.lean']
components = [
    'All native step-at-most-s piecewise representing bounded L2 families form an actual submodule of the original-law bounded families. Their image under the actual linear map into the completed ultrafilter Hilbert space is itself a submodule. Membership is equivalent to possessing a genuine native representative.',
    'Every native bounded piecewise representation is realized in that image for probability masses. The closure of the image equals its closed linear span. Divisibility of interval lengths gives inclusion of the represented images and their closed spaces, actual orthogonal projections and the exact nested energy identity.',
    'For every original-law [0,1]-valued target and every positive epsilon, its coarse orthogonal projection has a single actual native represented family within epsilon, globally [0,1]-valued at every stage and integer. Density comes from the genuine represented submodule closure and pointwise clipping contracts projection error by orthogonality.',
    'For nested native spaces with energy difference at most epsilon squared, the same clipped coarse representative has fine projected residual at most 2 epsilon. This discharges the analytic approximation step conditional on the actual energy selection.'
]
remaining = ('Native geometry, original-law Hilbert construction, native finite product/common representation and uniform per-family bounds remain proved. The actual native represented image is now a Hilbert submodule, its closure is its closed span, refinement yields nested projections, and actual [0,1]-valued native families approximate the coarse projection with the fine residual bounded by 2 epsilon under the energy-gap hypothesis. Next instantiate the finite simultaneous choices and Ramsey selection with the paper padding/principal tuple indexing and original block laws. Calibration/Alignment, subgroup inverse inputs, actual coloring/arithmetic data, ordered positive rapidly separated monochromatic witnesses and quantitative bounds where required remain. Bounds proved so far are existential per finite family. Original models, groups, Gamma, laws and StrongConjecture are unchanged. The full target remains unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start = source.index('MODULES = ')
end = source.index('\n\ndef declarations', start)
source = source[:start] + 'MODULES = ' + repr(modules) + '\nCOMPONENTS = ' + repr(components) + '\nREMAINING = ' + repr(remaining) + '\n' + source[end:]
review = [
    'PROGRESS. Previous round rechecked before edits, and all 958 baseline source/config hashes verified at registration. Retained proof files, original target, dependencies and source pin remain unchanged.',
    'Reviewed against fixed 05_prediction.tex, paragraphs defining N_i,l and proof of the energy-selection lemma. Actual represented images are proved linear using original native product representations, so their closure consists of limits of single actual representations, not merely an abstract enlarged generating set.',
    'The image uses the original finite-mass L2 spaces and actual hilbertFamilyCompletionLinearMap. No replacement law, unproved density hypothesis or extra Hilbert model is introduced. The membership equivalence is definitional.',
    'Probability normalization is used only where needed to turn uniformly bounded raw sequences and clips into bounded L2 families. Linear closure and nested projection identities hold for arbitrary nonnegative original finite masses.',
    'The native representation universe is explicit throughout. Nilpotence class is bounded by the same s; each witness retains its full native data, original discrete cocompact lattice and compatible quotient metric.',
    'Dense approximation uses Metric.mem_closure_iff on the actual submodule closure. The chosen vector is unpacked into its native family and clipped pointwise; thus the conclusion supplies an actual globally [0,1]-valued representative rather than only a point in the completed space.',
    'The target needs [0,1] bounds only on each original measure support. Weighted pointwise clipping contracts distance there. Since both representatives belong to the same coarse closed space, the proved Pythagorean comparison transfers contraction to distance from its projection.',
    'The fine residual estimate uses actual native subspace inclusion and the exact energy identity. Its energy-gap premise is explicit and has not yet been supplied by the paper-indexed Ramsey construction. Finite simultaneous choices across blocks, Calibration/Alignment and the main arithmetic conclusion remain.',
    'All 15 new declarations, including the projection instance, are individually registered for kernel axiom reports. No new axioms, omitted proof or modified original target are permitted.'
]
start = source.index('        application_review=[')
end = source.index('], new_modules=MODULES', start) + 1
source = source[:start] + '        application_review=' + repr(review) + source[end:]
Path('round-native-hilbert-span-audit.py').write_text(source, encoding='utf-8')
print('Prepared two-module audit: 11 theorems, 3 definitions, 1 instance, 15 reports.')
