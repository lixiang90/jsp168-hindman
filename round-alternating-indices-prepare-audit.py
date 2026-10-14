from pathlib import Path
import re

source = Path('round-indexed-energy-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = 'round-indexed-energy'", "PREFIX = 'round-alternating-indices'")
source = source.replace("OLD = 'round-native-hilbert-span'", "OLD = 'round-indexed-energy'")
counts = {'960':'963','963':'965','945':'947','954':'956','4645':'4657','10':'12','6':'9'}
# Restrict replacements to standalone numerals; restore the date after replacing 10.
source = re.sub(r'\b(?:960|963|945|954|4645|10|6)\b', lambda m: counts[m[0]], source)
source = source.replace('2026-12-12', '2026-10-10')
source = source.replace('new_definitions=4', 'new_definitions=3')
source = source.replace('new_module_count=3', 'new_module_count=2')
modules = ['Hindman168/AlternatingEnergyIndices.lean', 'Hindman168/AlternatingEnergySelection.lean']
components = [
    'An increasing 2n-tuple supplies padding k_u at even positions and principal j_u at odd positions. The actual inequalities k_u<j_u<k_v for u<v, monotonicity of padding and strict monotonicity of principal indices are proved.',
    'For tails contained in the principal set and lying below the first principal j_v, all tail entries lie below its padding k_v. The principal set has cardinality n and each such tail has cardinality less than n, proving the required energy-tuple size bound n+1.',
    'Uniform alternating energy selection is now proved: before all energy data a finite master bound is chosen, and an actual increasing 2n-tuple below it compares the energies at k_v and k_u for every v<=u and every valid principal tail simultaneously. The actual projection theorem allows pivot-dependent Hilbert spaces with the same target and original pivot in both energies.'
]
remaining = ('Native geometry, original-law Hilbert realization, native representation closure and clipped approximation remain proved. Alternating padding/principal selection is now proved with exact ordering, automatic tail-cardinality bounds and uniform simultaneous energy comparison, including empty tails and v=u. Next instantiate this selection with actual native original-law spaces, choose simultaneous clipped models and assemble their common finite native representation bounds. Calibration/Alignment, subgroup inverse inputs, actual coloring/arithmetic extraction, ordered positive rapidly separated monochromatic witnesses and required quantitative bounds remain. Original StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.')
start = source.index('MODULES = ')
end = source.index('\n\ndef declarations', start)
source = source[:start] + 'MODULES = ' + repr(modules) + '\nCOMPONENTS = ' + repr(components) + '\nREMAINING = ' + repr(remaining) + '\n' + source[end:]
review = [
    'PROGRESS. Previous round rechecked before edits. All 963 retained source/config hashes checked at registration. Prior proofs, original target, source pin and dependency versions remain intact.',
    'The paper labels a homogeneous set of size 2n alternately by padding and principal indices. We use its actual increasing order embedding from Fin (2*n), rather than assuming an ordered selection exists. Membership in the selected finite master interval is proved for every selected position.',
    'Padding and principal coordinates are respectively 2*u and 2*u+1. Fin bounds, strict ordering between successive pairs and monotonicity are kernel checked, including n=0 where the index type is empty.',
    'A tail contained in the principal image cannot lie between the padding and principal of its first pivot. Strict monotonicity recovers an earlier position and proves its principal value is below that padding. Missing the first pivot makes the tail a strict subset of the n-element principal set.',
    'Tuple size is thus at most n+1 without a new cardinality assumption. Comparisons are simultaneous for all principal tails and v<=u; equality v=u and empty tails are handled by the same statement.',
    'The master bound is fixed before the energy function. Both compared projection energies use x(T,j_u,a) in E(j_u); different pivot Hilbert spaces are allowed. Actual native subspace instantiation and simultaneous representatives remain subsequent work.',
    'Three definitions and nine theorems receive individual kernel axiom reports. No extra axiom, target weakening, completed main result or unavoidable blocker is claimed.'
]
start = source.index('        application_review=[')
end = source.index('], new_modules=MODULES', start) + 1
source = source[:start] + '        application_review=' + repr(review) + source[end:]
Path('round-alternating-indices-audit.py').write_text(source, encoding='utf-8')
print('Prepared two-module audit: 9 theorems, 3 definitions, 12 reports.')
