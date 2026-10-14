from pathlib import Path
import re

source = Path('round-projection-gap-energy-audit.py').read_text(encoding='utf-8')
source = source.replace('Hilbert projection and Ramsey energy increment', 'original-law ultrafilter Hilbert construction')
source = source.replace("PREFIX = 'round-projection-gap-energy'", "PREFIX = 'round-ultrafilter-inner-core'")
source = source.replace("OLD = 'round-native-lie-layer-compact'", "OLD = 'round-projection-gap-energy'")
counts = {'930': '933', '933': '939', '915': '921', '924': '930', '4475': '4517', '12': '42'}
source = re.sub(r'\b(?:930|933|915|924|4475|12)\b', lambda m: counts[m[0]], source)
source = source.replace("for kind, _ in values) == 42", "for kind, _ in values) == 21")
source = source.replace("'theorem_count': 42", "'theorem_count': 21")
source = source.replace('new_theorems=42, new_definitions=0', 'new_theorems=21, new_definitions=10, new_instances=11')
source = source.replace('new_module_count=3, new_theorem_count=42', 'new_module_count=6, new_theorem_count=21')
modules = ['BoundedHilbertFamilies', 'UltrafilterInnerCore', 'UltrafilterHilbertCompletion',
           'UltrafilterHilbertEmbedding', 'FiniteMassL2Space', 'FiniteMassUltrafilterHilbert']
components = [
    'Uniformly norm-bounded families in VARYING real seminormed inner product spaces form an actual vector submodule. Their pairings are uniformly bounded by Cauchy-Schwarz and have actual real ultrafilter limits by compactness.',
    'The actual ultralimit pairing is proved symmetric, positive semidefinite, additive and real-linear. Its genuine seminorm supplies a separated complete real Hilbert space, with a dense linear canonical map preserving the ultralimit inner product.',
    'The canonical images are equal IFF squared coordinate distances tend to zero along the specified ultrafilter. Uniform coordinate norm bounds pass to the completion. The canonical free hyperfilter extends atTop, so ordinary scalar pairing limits give the same Hilbert pairing.',
    'Original nonnegative finitely supported masses now supply actual coordinate L2 seminorms: squared norm is exactly the original weighted expectation of the square. Probability masses and supportwise bounded functions give uniformly bounded coordinate vectors. No counting law, normalization or deletion of zero-weight coordinates is substituted.',
    'Instantiating the completed Hilbert construction on ANY original sequence of nonnegative finite masses gives pairing exactly equal to the ultralimit of the original weighted expectations. Equality of vectors is exactly vanishing original weighted squared distance; ordinary pairing limits pass to the fixed free-hyperfilter Hilbert space.'
]
remaining = (
    'Original native lower-central geometry, specified-lattice quotients and cube compactness remain proved. '
    'The abstract Hilbert energy identities, clipping approximation and uniform finite Ramsey selection remain proved. '
    'The AMBIENT Hilbert construction is NOW PROVED: actual uniformly L2-bounded families for varying original '
    'nonnegative finite laws, actual ultrafilter pairing, zero-distance identification and separated complete '
    'Hilbert space with dense linear realization, original expectation pairing and ordinary-limit compatibility. '
    'Next construct actual bounded-complexity piecewise nilsequence families inside this space, their closed '
    'spans, nesting and closure under representing operations/clipping, then instantiate projection selection '
    'with finite common complexity and the paper\'s padding/principal tuple indexing. Remaining full-target '
    'work also includes Calibration/Alignment, subgroup inverse inputs, actual coloring/arithmetic data and '
    'ordered positive rapidly separated monochromatic witnesses, and quantitative degree/denominator bounds '
    'where required. Original model, group, Gamma, sampling laws and StrongConjecture remain unchanged. '
    'StrongConjecture and the prize target remain unproved. No unavoidable blocker is established; '
    'publication, PR and prize application remain pending.'
)
start = source.index('MODULES = ')
end = source.index('\n\ndef declarations', start)
source = source[:start] + 'MODULES = ' + repr(['Hindman168/'+m+'.lean' for m in modules]) + '\n' + \
    'COMPONENTS = ' + repr(components) + '\nREMAINING = ' + repr(remaining) + '\n' + source[end:]
review = [
    'PROGRESS. Previous audit rechecked before edits. All 933 retained source/config hashes checked before registration; only root imports and registry change. No retained proof, original statement, model, lattice, law, pinned dependency or attributed source is modified.',
    'The source route is the actual Hilbert-space paragraph of 05_prediction.tex immediately before nested-spaces. The coordinate spaces can vary with w and may be SEMInormed, permitting original zero-mass coordinates. Every family has one finite norm bound valid for all w; this is not an unbounded Cartesian product.',
    'Cauchy-Schwarz bounds each scalar pairing by the product of two uniform norm bounds. The image ultrafilter lies in a compact real interval, giving genuine convergence to limUnder. Bilinearity and positivity use convergence and Hausdorff uniqueness, rather than an unproved limit functional or arbitrary choice of scalar values.',
    'Positive semidefiniteness is established before quotient/completion. The UltrafilterFamily type synonym deliberately prevents coordinatewise product topology inference. Its seminorm comes ONLY from the proved ultralimit core. The complete space inherits this exact uniform structure, and inner preservation is checked explicitly by Completion.inner_coe.',
    'The canonical map is a genuine real linear map with dense range. Its squared norm equals the ultralimit self-pairing. The squared-distance limit proves both directions of the equality/zero-distance equivalence, so zero-norm families are identified and distinct vectors cannot survive with zero norm. This is the separated completion required in the paper.',
    'The fixed Filter.hyperfilter on natural numbers extends atTop by the library theorem Nat.hyperfilter_le_atTop. All ordinary scalar pairing limits therefore agree with the chosen free-ultrafilter pairing. No false claim of ordinary convergence is made from ultrafilter convergence.',
    'FiniteMassL2 uses exactly expectation mu (f*g), with nonnegativity checked for the given mass. The squared norm equals expectation mu (f^2). The probability-bound theorem uses total mu=1 only for the uniform norm estimate; the space construction does not normalize mass. The function bound is needed only on the actual support.',
    'FiniteMassUltrafilterHilbert instantiates the actual completed Hilbert space on the original mass family, with pairing exactly the original expectation ultralimit and equality exactly vanishing original mean squared distance. These identities certify the intended law, not a merely isomorphic unrelated probability model.',
    'Actual bounded-complexity nilsequence representing families and their closed-span nesting, clipping stability, finite complexity bounds, tuple selection, Calibration/Alignment and StrongConjecture remain to be proved. No unavoidable blocker, full-target claim, publication or prize submission is asserted.'
]
start = source.index('        application_review=[')
end = source.index('], new_modules=MODULES', start) + 1
source = source[:start] + '        application_review=' + repr(review) + source[end:]
Path('round-ultrafilter-inner-core-audit.py').write_text(source, encoding='utf-8')
print('Prepared six-module audit: 21 theorems, 10 definitions, 11 instances, 42 reports.')
