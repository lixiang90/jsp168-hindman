from pathlib import Path
import re

source = Path('round-native-lie-layer-compact-audit.py').read_text(encoding='utf-8')
source = source.replace('original lower-central geometry increment', 'Hilbert projection and Ramsey energy increment')
source = source.replace("PREFIX = 'round-native-lie-layer-compact'", "PREFIX = 'round-projection-gap-energy'")
source = source.replace("OLD = 'round-rational-subgroup-character'", "OLD = 'round-native-lie-layer-compact'")
counts = {'923': '930', '930': '933', '912': '915', '921': '924', '4463': '4475', '28': '12', '27': '12'}
source = re.sub(r'\b(?:923|930|912|921|4463|28|27)\b', lambda m: counts[m[0]], source)
source = source.replace('new_definitions=1', 'new_definitions=0').replace('new_module_count=7', 'new_module_count=3')
modules = ['NestedProjectionEnergy', 'RamseyEnergySelection', 'RamseyProjectionSelection']
components = [
    'Genuine nested orthogonal projections satisfy the exact squared-distance/energy-difference identity, energy monotonicity and the paper\'s 2 epsilon fine-projection error bound from coarse approximation.',
    'Pythagorean decomposition proves that any representative-preserving clipping which contracts distance to the original vector also contracts distance to its orthogonal projection. Density then supplies clipped representatives with any prescribed positive accuracy and the stated clipping predicate.',
    'A uniform finite Ramsey bound is proved for simultaneously binned [0,1] energies with arbitrary finite labels and every tuple cardinality up to K. The finite bound is selected BEFORE all energy data, depends only on labels/K/desired size/bin width, and gives strict bin-width closeness.',
    'The uniform energy selector is instantiated on genuine Hilbert-space projection energies of unit-bounded vectors, then yields the 2 epsilon model-error estimate whenever the selected pair has nested subspaces and the same vector. No actual nilsequence space or ultralimit is assumed to have been constructed by this abstract lemma.'
]
remaining = (
    'Original native lower-central geometry, specified-lattice quotients and canonical cube compactness remain proved. '
    'The original-law model-error testing interface has no supplied layer-compactness premise. The abstract '
    'Hilbert-space energy identity, clipping approximation and uniform finite Ramsey gap-energy selection are NOW '
    'PROVED with the correct bound-before-data quantifiers. The actual ultrafilter/completed Hilbert space, '
    'piecewise nilsequence closed spans, their nesting and closure under representing operations/clipping still '
    'must be constructed and plugged into these lemmas, with finite common complexity and the paper\'s '
    'padding/principal tuple indexing. Remaining full-target work also includes Calibration/Alignment, '
    'subgroup inverse inputs, actual coloring/arithmetic data and ordered positive rapidly separated '
    'monochromatic witnesses, and quantitative degree/denominator bounds where required. The original model, '
    'group, Gamma and StrongConjecture statement remain unchanged. StrongConjecture and the prize target '
    'remain unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'
)
start = source.index('MODULES = ')
end = source.index('\n\ndef declarations', start)
source = source[:start] + 'MODULES = ' + repr(['Hindman168/'+m+'.lean' for m in modules]) + '\n' + \
    'COMPONENTS = ' + repr(components) + '\nREMAINING = ' + repr(remaining) + '\n' + source[end:]
review = [
    'PROGRESS. The preceding audit was rechecked before edits. All 930 baseline hashes are checked at registration. Only root imports and axiom registry change among retained source/config files; original statements, geometry, arithmetic and all retained proofs stay intact.',
    'The source route is section 05_prediction.tex, nested-spaces equation and Ramsey selection of gap energies lemma. The new declarations prove their Hilbert identities and uniform selection mechanism, not the existence of the actual ultralimit or nilsequence spaces.',
    'The nested projection identity uses the genuine mathlib orthogonal projection, its composition for U <= V, and the orthogonal-complement Pythagorean decomposition. The sign is fine-space energy minus coarse-space energy. Nonnegativity is proved, not assumed. The 2 epsilon bound uses the same vector and a model lying in the coarse space.',
    'The clipping lemma compares squared distances to the original vector and cancels the SAME perpendicular residual in two exact Pythagorean identities. The representative existence theorem explicitly assumes density, closure under clipping, clipping contraction and its output predicate. These are obligations for the actual representing families and are not hidden in a claimed nilsequence construction.',
    'Natural floor bins handle both endpoints of [0,1], including energy=1. The finite palette has floor(1/delta)+1 bins per label. Equal bins imply STRICT distance < delta via lower and upper floor inequalities and delta>0. No unjustified bound or unbounded color set enters Ramsey.',
    'The joint palette is the finite function type from labels to bins. The retained finite size-homogeneous Ramsey theorem selects N before the arbitrary energy function. All equal-cardinality subsets up to K and all labels share the estimate. Empty label types and size-zero cases are permitted without fabricating colors.',
    'Projection energy lies in [0,1] by the genuine operator contraction and the input vector norm bound. Selection uses delta=epsilon^2. The model-selection theorem explicitly requires equal vectors and nested spaces for a selected pair, preserving the same-vector condition required by the energy identity. Actual tail/padding tuple decoding remains to be supplied.',
    'No full Calibration/Alignment, ultrafilter Hilbert completion, common-complexity actual nilsequence model, inverse theorem or final StrongConjecture is claimed. The task remains active, with no unavoidable blocker established.'
]
start = source.index('        application_review=[')
end = source.index('], new_modules=MODULES', start) + 1
source = source[:start] + '        application_review=' + repr(review) + source[end:]
Path('round-projection-gap-energy-audit.py').write_text(source, encoding='utf-8')
print('Prepared three-module audit: 12 theorems, zero definitions.')
