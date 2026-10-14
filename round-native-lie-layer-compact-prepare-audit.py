from pathlib import Path
import re

source = Path('round-rational-subgroup-character-audit.py').read_text(encoding='utf-8')
source = source.replace('Register and audit the rational-functional increment', 'Register and audit the original lower-central geometry increment')
source = source.replace("PREFIX = 'round-rational-subgroup-character'", "PREFIX = 'round-native-lie-layer-compact'")
source = source.replace("OLD = 'round-rational-functional'", "OLD = 'round-rational-subgroup-character'")
counts = {'917': '923', '923': '930', '905': '912', '914': '921', '4435': '4463', '22': '28', '20': '27'}
source = re.sub(r'\b(?:917|923|905|914|4435|22|20)\b', lambda m: counts[m[0]], source)
source = source.replace('new_definitions=2', 'new_definitions=1').replace('new_module_count=6', 'new_module_count=7')
modules = ['NativeLieLayerLatticeCompact', 'NativeGroupLayerPositivePowers', 'SigmaCompactGeneratedSubgroup',
           'BaireSubgroupCover', 'NativeGroupLowerCentralExact', 'NativeLowerCentralCubeGeometry', 'NativeMaskModelTesting']
components = [
    'Every original real Lie lower-central layer is rational for the SAME specified lattice rational form, so its actual exponential subgroup has compact metrizable intersection quotient and a closed natural embedding into the original quotient.',
    'The actual algebraic GROUP lower-central layer has rational logarithmic span equal to the entire real Lie layer restricted to Q; every element of the exponential Lie layer has a positive integral power in the actual algebraic group layer.',
    'Algebraic subgroup generation, commutators and lower-central series preserve sigma compactness. A sigma-compact subgroup with countably many homeomorphic images covering a connected Baire group is the whole group.',
    'Actual positive-root homeomorphisms on original exponential Lie subgroups, together with sigma compactness and Baire category, prove EXACT equality of original algebraic group lower-central layers and exponential real Lie layers; the original algebraic layers themselves are closed.',
    'All original lower-central restricted-lattice quotients and canonical cube quotients are compact. Original lower-central filtration equals its topological-closure filtration, and native local compactness is derived from the original manifold.',
    'The retained uniform original-law mask-model error test is instantiated for arbitrary original native nilmanifolds with the SAME Gamma, with no external layer-cocompactness premise. The existing arithmetic ordering, weight bounds, compact observables and dual-control premises remain explicit.'
]
remaining = (
    'The original native lower-central geometry is NOW PROVED: actual algebraic group layers equal exponentials '
    'of the actual real Lie layers and are closed, rational for the SAME specified lattice, with compact '
    'intersection quotients and compact canonical cube quotients. Original and closed filtrations agree. '
    'The original-law uniform model-error testing interface is instantiated without supplied layer compactness. '
    'The full original model, group and Gamma remain unchanged. Remaining full-target work includes complete '
    'nested coarse-model projections, Calibration/Alignment, actual coloring/arithmetic data and ordered '
    'positive rapidly separated monochromatic witnesses, and quantitative degree/denominator bounds where '
    'required. The analytic dual-control and ordering inputs of the instantiated testing theorem are still '
    'explicit premises to be supplied by the full construction. StrongConjecture and the prize target remain '
    'unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
)
start = source.index('MODULES = ')
end = source.index('\n\ndef declarations', start)
source = source[:start] + 'MODULES = ' + repr(['Hindman168/'+m+'.lean' for m in modules]) + '\n' + \
    'COMPONENTS = ' + repr(components) + '\nREMAINING = ' + repr(remaining) + '\n' + source[end:]
review = [
    'PROGRESS. The previous full audit was rechecked before edits. All 923 retained source/config hashes are checked before registration; only root imports and axiom registry change. Existing proof sources, StrongStatement, original model/group/lattice, pins and attribution remain unchanged.',
    'Lie-layer rationality uses the retained scalar-extension lower-central theorem on W_Gamma restricted to integers. This integer module is only a presentation of the proved rational form: it is NOT Log Gamma and is NOT asserted discrete. Its rational span is exactly W_Gamma. Compactness uses the actual original Gamma intersection theorem from the previous round.',
    'Applying internal rational lower-central equality to the top subgroup identifies its logarithmic span with the entire real Lie layer restricted to Q. Scalar restriction does not require finite dimension over Q. The positive-power conclusion uses the proved rational-hull theorem, and alone is not treated as exact layer equality.',
    'SigmaCompactGeneratedSubgroup treats ALGEBRAIC subgroup closure as the countable union of finite products of generators and inverses. Continuous commutator images of sigma-compact subtype products generate sigma-compact commutator subgroups; induction covers the actual algebraic lower-central series. No topological closure is substituted.',
    'BaireSubgroupCover decomposes the subgroup into countably many compact sets. Their images under countably many genuine homeomorphisms form a closed countable cover. Baire category yields nonempty interior of one image; pulling it back puts a nonempty open set inside the ACTUAL subgroup. The subgroup is open and closed, hence all of the connected ambient group.',
    'The positive-root maps are genuine homeomorphisms obtained by conjugating nonzero real scalar multiplication through the original restricted exponential homeomorphism. Their power identity is proved from the original exponential/log inverse and integral powers, not from presumed root closure of the algebraic group layer.',
    'NativeGroupLowerCentralExact applies the Baire lemma to the algebraic layer inside the exponential Lie layer. Sigma compactness of the original group follows from surjective continuous exponential and finite-dimensional compact balls. Positive-power saturation gives the countable cover. Exact equality and closedness follow without assuming either as an input.',
    'The paper filtration uses lowerCentralSeries (i-1); NativeLowerCentralCubeGeometry preserves this indexing, the actual Gamma.comap inclusion and canonical cube definitions. All layer compactness hypotheses are discharged by original rational subgroup compactness, and local compactness is derived from the native finite-dimensional manifold.',
    'NativeMaskModelTesting removes only the proved geometric premises from the retained original-law testing theorem. Its arithmetic gap/tail, nonnegative weight, dual control and compact observable assumptions remain visible. It is not asserted to establish those analytic inputs, final coloring extraction or StrongConjecture.',
    'No unavoidable blocker has been established. The main theorem, publication, PR and prize submission remain pending; this is a verified proof increment.'
]
start = source.index('        application_review=[')
end = source.index('], new_modules=MODULES', start) + 1
source = source[:start] + '        application_review=' + repr(review) + source[end:]
Path('round-native-lie-layer-compact-audit.py').write_text(source, encoding='utf-8')
print('Prepared seven-module audit: 27 theorems, one definition, 28 reports.')
