from pathlib import Path
import re

prefix = 'round-rough-sampling-weights'
stems = ['RoughCoprimeResidueIntersection', 'RoughNormalizedCountError',
    'RoughNormalizedPieceWeights', 'RoughIntervalPieceComparison',
    'RoughProbabilityProductError', 'RoughBoxPieceWeights',
    'RoughFiniteBoxWeightComparison', 'RoughUniformFiberMixture',
    'RoughResiduePieceNonempty', 'RoughUniformFiberSelection']
modules = ['Hindman168/' + s + '.lean' for s in stems]
components = [
    'RoughCoprimeResidueIntersection constructs an actual simultaneous integer residue from the proved modular inverse of t modulo K. When t and K are coprime, the exact original intersection of interval classes modulo t and K equals one class modulo tK. Its location-independent count differs from length/(tK) by at most one.',
    'RoughNormalizedCountError proves positivity of the actual step-class denominator and a quantitative normalized residue error at most 4t/length when length is at least 2t. It retains the actual numerator and denominator counts and does not substitute the expected denominator into a ratio.',
    'RoughNormalizedPieceWeights proves the general normalized partial-count bound and applies it to the actual step-t/K intersection in any integer subinterval of the original interval. Its weight differs from the geometric proportion sublength/(length*K) by at most 4t/length.',
    'RoughIntervalPieceComparison compares actual original step-t and unrestricted integer weights of a subinterval with a prescribed K residue. Their absolute weight difference is at most 5t/length, uniformly in every signed endpoint and residue.',
    'RoughProbabilityProductError proves an elementary telescoping bound for finite products of factors of absolute value at most one. The product difference is at most the sum of the individual absolute differences, without a factor exponential in the dimension.',
    'RoughBoxPieceWeights proves the actual coordinate intersection cardinality product and rewrites the actual box count ratios as products of coordinate count ratios. It bounds the weight difference of one rectangular subbox and residue vector by the sum of 5t/side_length over the fixed coordinates.',
    'RoughFiniteBoxWeightComparison sums the actual rectangular piece-weight differences. If original sides are at least cZ and 2t is at most cZ, the sum is at most card(pieces)*dimension*5t/(cZ). All endpoints, sample residues and piece choices remain arbitrary subject to the actual containment hypotheses.',
    'RoughUniformFiberMixture proves the exact original uniform finite sampling law is a mixture of its actual label fibers, weighted by their actual cardinalities divided by the original cardinality. It proves weight sum one for a nonempty parent and exact expectation disintegration for signed tests, including empty fibers of zero weight.',
    'RoughResiduePieceNonempty proves positivity of every actual interval and box intersection piece when each subbox side is at least 2tK, using the actual coprime intersection and count theorem. This supports conditioning on the later geometric pieces.',
    'RoughUniformFiberSelection bounds actual uniform fiber test expectations from support-wise bounds, including empty fibers. It combines exact original expectation disintegration and reweighted convex selection to select a positive-cardinality original fiber retaining the prescribed discrepancy threshold. The discrepancy threshold is not divided by the number of pieces.',
]
remaining = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'Actual coprime interval/box residue weights, quantitative O(t/Z) finite-piece weight comparison, positive piece sizes under explicit side thresholds, and exact original uniform finite fiber mixtures and convex selection are now proved. '
    'Construct the bounded rectangular subbox partition with the required upper and lower side bounds and prove its label fibers are exactly these box/residue pieces. '
    'Assemble the geometric label, actual weight comparison, freezing and uniform induced-test Lipschitz approximation into the original chosen-piece descent, with all error losses explicit; connect uniform rough-step asymptotics to the side thresholds and total weight error. '
    'Package the smaller rational character kernel as native nilmanifold data with the proved compatible source metric and strict dimension decrease. '
    'The quantitative Leibman obstruction, affine substituted-polynomial coefficient identity, corrected box comparison, stretched-filtration prerequisites, finite density extraction, dimension induction and uniform rough-step comparison remain open. '
    'Package finite native readings and connect conditional face laws. Buffered short-bin geometry, prior-event positive probability, extra-conditioning posterior control, quantitative native smooth-observable bounds, conditional face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
source = Path('round-rough-induced-approximation-audit.py').read_text(encoding='utf-8')
for name, value in {'PREFIX': prefix, 'OLD': 'round-rough-induced-approximation',
        'MODULES': modules, 'COMPONENTS': components, 'REMAINING': remaining}.items():
    source, count = re.subn('^' + name + r'\s*=.*$', lambda _: name + ' = ' + repr(value), source, flags=re.M)
    assert count == 1, name
a = source.index('application_review=COMPONENTS+')
b = source.index('verified=summary', a)
review = [
    'Section 06 splits both original sampling laws into subboxes and residue vectors. The new count and weight bounds use the actual original finite interval/box classes. Negative integer endpoints and arbitrary residues remain permitted. Coprimality is explicit and used to prove the intersection is a single class modulo tK.',
    'The normalized denominator is the actual original step-t class cardinality. From count error <=1 and length/t>=2 it is at least half the expected count and is positive. The resulting 4t/length bound accounts for both numerator and denominator errors.',
    'The unrestricted piece weight uses its actual original full integer interval/box cardinality. Its own numerator error is at most 1/length. Combining the two gives 5t/length. The common expected piece proportion is sublength/(length*K), not a replacement sampling law.',
    'Actual coordinate product classes and their intersections are used. Each normalized factor is in [0,1] by actual finite set containment. Telescoping products therefore gives a sum of coordinate errors. Empty coordinate types yield singleton boxes and zero error, as required.',
    'The finite-piece bound is valid even for overlapping listed subboxes; it is only a numerical bound on the listed weights. To identify them as a convex partition one must still construct a geometric label and prove its fibers equal those pieces. This obligation remains explicit.',
    'The constant card(pieces)*dimension*5/c is fixed only if the number of pieces, dimension and c are fixed before varying samples and endpoints. No uniformity over unbounded numbers of pieces is claimed. The independent convex selection threshold does not divide discrepancy by card(pieces).',
    'Exact uniform label-fiber disintegration is proved as an equality of actual finite masses, not just events or approximate averages. Empty fibers are zero-weight zero-mass components. Nonempty parent mass normalization follows from actual fiber weights; selected source fiber has positive cardinality.',
    'The actual uniform-fiber selection theorem allows an empty comparison support algebraically, while the intended two-probability application requires a nonempty comparison parent. Nonempty residue pieces have a separate proved threshold of side >=2tK. Their geometric and asymptotic application remains to be assembled.',
    'These supporting results do not establish the full geometric partition, descent assembly, smaller native-data packaging, uniform dimension induction or StrongConjecture. The old unproved inverse and recurrence existence inputs remain unchanged.',
    'All retained source hashes and transitive axiom sets are unchanged. These are author-side checks, not independent kernel replay.',
]
source = source[:a] + 'application_review=COMPONENTS+' + repr(review) + '+[REMAINING],\n        ' + source[b:]
source = re.sub("reference_scope='[^']*'", "reference_scope='06_rough_progressions actual coprime residue sampling weights and exact original convex fiber disintegration'", source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print('Prepared audit for', len(modules), 'modules.')
