from pathlib import Path
import re

source = Path('round-native-hilbert-span-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-native-hilbert-span'", "PREFIX = 'round-indexed-energy'")
source = source.replace("OLD = 'round-native-product-data'", "OLD = 'round-native-hilbert-span'")
counts = {'958':'960','960':'963','942':'945','951':'954','4635':'4645','15':'10','11':'6'}
source = re.sub(r'\b(?:958|960|942|951|4635|15|11)\b', lambda m: counts[m[0]], source)
source = source.replace('new_definitions=3', 'new_definitions=4').replace('new_instances=1', 'new_instances=0')
source = source.replace('new_module_count=2', 'new_module_count=3')
modules = ['Hindman168/EnergyTupleEncoding.lean', 'Hindman168/IndexedEnergySelection.lean', 'Hindman168/IndexedProjectionSelection.lean']
components = [
    'The actual increasing energy tuple T,l,i is encoded by insert i (insert l T). With every tail entry below l<i, its maximum recovers i, the maximum after deleting i recovers l, and deleting both recovers exactly T. Its cardinality is T.card+2 and subset membership is preserved.',
    'Uniform finite Ramsey selection now applies to exact tail-gap-pivot energy data. The master bound is chosen before all bounded energy data. On the homogeneous set, energies with the same T,i and different valid gaps l,k differ by less than delta, simultaneously for all finite labels.',
    'Projection selection supports a different real Hilbert space for every pivot i. The two compared tuples use exactly the same x(T,i,a) and pivot space, so no equality between targets from different tuples is postulated. Nested spaces and coarse epsilon approximants give the fine projected residual bound 2 epsilon.'
]
remaining = ('Native geometry, Hilbert realization, native finite product closure, actual clipped dense approximation and its conditional fine residual estimate remain proved. Exact tail-gap-pivot tuple encoding and uniform indexed Ramsey energy/projection selection are now proved, including pivot-dependent Hilbert spaces and the same target vector in both compared energies. Next extract alternating padding/principal indices from the homogeneous set, instantiate the native spaces and original block laws, and assemble simultaneous actual representatives with common finite bounds. Calibration/Alignment, subgroup inverse inputs, actual coloring/arithmetic extraction, ordered positive rapidly separated monochromatic witnesses and required quantitative bounds remain. Original StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start = source.index('MODULES = ')
end = source.index('\n\ndef declarations', start)
source = source[:start] + 'MODULES = ' + repr(modules) + '\nCOMPONENTS = ' + repr(components) + '\nREMAINING = ' + repr(remaining) + '\n' + source[end:]
review = [
    'PROGRESS. Previous round rechecked before editing. All 960 retained hashes checked at registration; only root imports and axiom registry change among baseline files. Original statements, original laws, dependencies and fixed source remain unchanged.',
    'The paper energy-selection argument colors increasing tuples with tail T followed by gap l and pivot i. Encoding by a finite set is valid because all tail entries precede l<i. Explicit decoding, cardinality and subset theorems establish the bridge to the finite-set Ramsey theorem.',
    'A sup on natural numbers defines the total decoder even on empty or singleton sets. Invalid tuples cause no problem: the energy function is globally bounded, while decoding identities are used only for valid tuples. No assumption that an arbitrary finite set has two distinct largest elements is made.',
    'The compared finite sets both have cardinality T.card+2. Their recovered tails and pivots coincide exactly, even when l=k. Both gap entries and the pivot belong to the selected set. This rules out the erroneous comparison of projections of unrelated target vectors.',
    'The uniform master bound is selected before energy data, projection spaces and vectors. The finite labels are jointly colored, and energy bin width is epsilon squared. The projection variant allows genuinely different Hilbert spaces at different pivots.',
    'The fine residual theorem explicitly requires the relevant space inclusion and coarse approximation. It derives the actual energy bound from the indexed homogeneous set and applies the previously proved projection identity. It does not yet instantiate the native original-law spaces or extract alternating padding indices.',
    'All four definitions and six theorems are individually kernel-audited. Full target, Calibration/Alignment, final arithmetic extraction, publication and prize submission remain uncompleted.'
]
start = source.index('        application_review=[')
end = source.index('], new_modules=MODULES', start) + 1
source = source[:start] + '        application_review=' + repr(review) + source[end:]
Path('round-indexed-energy-audit.py').write_text(source, encoding='utf-8')
print('Prepared three-module audit: 6 theorems, 4 definitions, 10 reports.')
