from pathlib import Path
import json

PREFIX = 'round-rough-stretched-filtration-weighted-difference'
OLD = 'round-rough-real-box-binomial-transfer'
MODULES = ['Hindman168/'+m+'.lean' for m in [
    'RoughStretchedFiltrationIndices', 'RoughStretchedLowerCentralFiltration',
    'RoughNativeStretchedFiltration', 'RoughNativeStretchedLieBracket',
    'RoughVectorWeightedDegree', 'RoughNativeWeightedPolynomial',
    'RoughTranslationTopCoefficients', 'RoughWeightedPolynomialDifference']]
COMPONENTS = [
    'Actual stretched group lower central filtration: natural ceiling indices are monotone and subadditive; the actual group layers start at the whole group, are normal and antitone, satisfy the commutator condition and terminate at s*D+1 for step at most s and positive fixed D.',
    'Actual native stretched group layers are identified by proved group/Lie lower central equality with the original exponential Lie layers. Closedness, contractibility, simple connectedness and exact original logarithm/exponential membership follow from this equality.',
    'Actual native stretched Lie layers are antitone and initially the whole model. The original native adjoint differential bracket adds stretched weights using the actual original Lie lower central bracket theorem and the ceiling inequality.',
    'A sufficient termwise weighted vector polynomial condition is proved stable under append, scalar multiplication and bilinear brackets that add weights. Its actual evaluations lie in the stated layer. Ordinary degree at most D gives the native initial condition; actual native brackets and exponential membership are connected.',
    'Translation preserves every scalar coefficient at or above the original total degree. The affine power coefficient formula becomes diagonal under the total-degree comparison. Every nonzero ordinary translation difference has strictly smaller total degree.',
    'The actual vector translation difference deletes exactly the zero scalar difference terms and evaluates to the true translated value minus the original value. Weighted ordinary differences increase the layer offset by one; actual affine substitutions preserve the weighted condition.'
]
previous = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))['last_round']['remaining']
REMAINING = previous.replace(
    'Group difference translation is proved; actual native logarithm polynomials still need the stretched lower-central filtration and actual BCH coefficient/difference membership. Existing nativeGroupLowerCentralSeries_eq_exponential and nativeLieLowerCentralSubgroup normality/closedness/contractibility can be reused when constructing the stretched family.',
    'The actual stretched group filtration, its original native Lie-layer equality and topology, native weighted brackets, initial bounded-degree coefficient condition and actual zero-filtered ordinary weighted differences are now proved. Actual native BCH cancellation and weighted group difference membership remain open; the sufficient termwise condition has not yet been propagated through the full BCH difference. Rationality of the actual stretched layers relative to the original lattice must still be assembled from actual rational log spans.')
assert REMAINING != previous
REVIEW = [
    'The stretch D is strictly positive in all substantive filtration and degree claims, as in the paper. D=0 is not a permitted polynomiality input. The layer formula uses ceil(i/D)-1 in mathlib lower central numbering and has the whole group at both i=0 and i=1.',
    'Commutator inclusion uses the actual lower central series, including its zero-index normality behavior. The terminal index s*D+1 is justified by a lower ceiling bound; it is not asserted merely from a degree heuristic.',
    'Native topological properties are transported through the already proved exact original group/Lie equality. No surrogate group, added instance, supplied filtration or unproved identification is introduced.',
    'Weighted degree is a sufficient condition on each scalar-polynomial/vector pair in the finite list representation. It can be stronger than the coefficient condition after cancellation. No equivalence to the paper coefficient condition is asserted.',
    'The native bracket is the original adjoint differential identified with the actual native Lie bracket. Its weighted inclusion uses both-input Lie lower central membership, not only a one-sided adjoint lowering estimate.',
    'A nonzero scalar translation difference has degree strictly below the original degree. Zero polynomials have natural totalDegree zero and are handled separately: their difference terms are deleted from the actual vector representation, with exact evaluation preserved.',
    'Ordinary difference increases the weighted offset by one, including cancellation and constant terms. Affine substitution only preserves the offset; no lowering is asserted for dilations.',
    'These results prove the filtration and ordinary weighted difference portions of the paper argument. Cancellation of the terms in native BCH(A+Delta,-A) containing no Delta, finite weighted BCH propagation, lattice-relative rationality and iterated actual group difference polynomiality remain open.',
    'The explicit equal-cube quantitative character obstruction, finite nonzero character construction and the two main existence inputs remain unproved. No new axiom is introduced to discharge them.',
    'Focused checks, full build, retained hashes and selected transitive axiom reports are author-side verification. All six pinned primary paper sections are compared; no independent kernel replay, complete target or prize eligibility is claimed.'
]
src = Path(OLD+'-audit.py').read_text(encoding='utf-8')
src = src.replace("PREFIX = '"+OLD+"'", "PREFIX = '"+PREFIX+"'")
src = src.replace("OLD = 'round-rough-equal-cube-box-transfer'", "OLD = '"+OLD+"'")
start = src.index('MODULES = ')
end = src.index('\ndef declarations():', start)
src = src[:start]+f'MODULES = {MODULES!r}\nCOMPONENTS = {COMPONENTS!r}\nREMAINING = {REMAINING!r}\n'+src[end:]
start = src.index('        application_review=COMPONENTS+')
end = src.index('\n        verified=summary', start)
src = src[:start]+f'        application_review=COMPONENTS+{REVIEW!r}+[REMAINING],'+src[end:]
src = src.replace("reference_scope='06_rough_progressions exact half-open real-box integer samples, ceil count/location budgets and conditional native finite character transfer'", "reference_scope='06_rough_progressions actual stretched lower central filtration and weighted ordinary polynomial differences; native BCH propagation still open'")
Path(PREFIX+'-audit.py').write_text(src, encoding='utf-8')
