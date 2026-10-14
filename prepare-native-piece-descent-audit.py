from pathlib import Path

PREFIX = 'round-rough-native-piece-descent'
OLD = 'round-rough-labelled-native-tests'
MODULES = ['UniformFiniteExpectationCongruence', 'RoughDependentRescaledSelection',
    'RoughNativeRescaledPieceSelection', 'RoughBalancedRescaledGeometry',
    'RoughNativeDescentPolynomial', 'RoughNativeModelDescentPolynomial',
    'RoughRescaledPieceGeometry', 'RoughNativePieceDescent', 'RoughFiniteLabelThinning',
    'RoughJointProgressionPolynomial', 'RoughPieceDescentThresholds',
    'RoughNativeKernelLabelThinning', 'RoughNativeModelPieceDescent']
MODULES = ['Hindman168/'+name+'.lean' for name in MODULES]
COMPONENTS = [
    'UniformFiniteExpectationCongruence proves actual finite uniform expectation congruence on the support, retaining the empty-support convention.',
    'RoughDependentRescaledSelection constructs a genuinely label-dependent quotient-test discrepancy on an exact rescaled piece, preserving both positive-cardinality supports. It combines original error control with convex piece selection and actual expectation congruence.',
    'RoughNativeRescaledPieceSelection supplies actual uniformly Lipschitz native quotient tests to that selection. Partition count and Lipschitz bound are fixed before all progression, coefficient, box, map and observable data; the discrepancy is not divided by the piece count.',
    'RoughBalancedRescaledGeometry proves balanced-piece lower sides after residue division, comparable sides at scale Z/K and original sample position bounds.',
    'RoughNativeDescentPolynomial combines actual subgroup native logarithm polynomial transfer, spatial affine substitution, strict finrank decrease and a degree bound depending only on original degree and nilpotence step.',
    'RoughNativeModelDescentPolynomial derives the horizontal splitting degrees from actual coefficient models and original scalar polynomial degrees, rather than assuming the generated rational model degree independently.',
    'RoughRescaledPieceGeometry bounds both actual signed transformed endpoints by (C+1)*Z/K, proves side lower bound c*Z/(4*N*K) and upper bound 4*C*Z/(N*K), and retains arbitrary original signed boxes.',
    'RoughNativePieceDescent constructs in one theorem the actual smaller native quotient, its all-real joint logarithmic polynomial with original-step degree bound, comparable rescaled boxes, positive-cardinality supports and retained discrepancy. It uses the actual previous freezing and induced-test constructions.',
    'RoughFiniteLabelThinning uses proved finite van der Waerden to make one finite label common along a long progression. Its smooth progression reparametrization preserves original roughness, the original dyadic interval and smoothness of the new positive difference.',
    'RoughJointProgressionPolynomial preserves the actual all-real joint logarithmic polynomial and total-degree bound under affine progression reparametrization, leaving spatial parameters unchanged.',
    'RoughPieceDescentThresholds derives one eventual threshold from actual power domination before every varying positive t<=2*S, simultaneously supplying all side and denominator bounds, Z/K>=1 and a fixed eta/2 discrepancy budget with freezing and approximation each eta/32.',
    'RoughNativeKernelLabelThinning fixes the actual residue vector and native quotient index on a long progression, then constructs its single all-real reparametrized native logarithm polynomial with strict finrank decrease and degree bound depending only on the original step and degree. The input predicate remains explicit; actual full bad-family construction is not asserted.',
    'RoughNativeModelPieceDescent specializes actual native piece descent to the generated rational coefficient models, deriving horizontal splitting and degree bounds from the original scalar polynomials. It retains the actual nonempty samples, smaller quotient, geometric bounds and discrepancy.'
]
REMAINING = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'Actual single-index native discrepancy descent is now assembled, including model-derived degree bounds, all-real native logarithms, strict finrank decrease, exact nonempty rescaled samples, endpoint and side bounds, and a uniform fixed discrepancy budget from power domination. '
    'Finite label thinning and actual kernel joint polynomial reparametrization now make residue vectors and quotient indices common along long progressions; smoothness and roughness preservation are proved. '
    'Assemble all per-index witnesses into the full smaller-dimensional bad progression family, retaining a common group map and a genuine scale subsequence for each length. '
    'The full quantitative Leibman obstruction and uniform finite nonzero character list, corrected arbitrary-box comparison, stretched-filtration prerequisites, finite density extraction, complete dimension induction and uniform rough-step theorem remain open. '
    'Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
REVIEW = [
    'This batch also completes and registers six drafts found outside the last recorded manifest. Every new source receives a fresh focused Lean check; no prior scratch run is counted as recorded verification.',
    'The actual new quotient is the original horizontal character kernel with its particular rational conjugate lattice intersection and original native metric. Distinct finite indices are not identified as the same quotient space.',
    'Finite mixture selection retains a fixed discrepancy theta when the total actual weight error and twice the original approximation error fit below the original discrepancy. No division by N^dimension*K^dimension is introduced.',
    'Both supports have positive cardinality, so the two actual selected uniform finite laws are probabilities. Original and rescaled test functions agree exactly on the respective supports.',
    'Both transformed endpoints are bounded, not just integer samples. The c/(4*N) lower-side constant spends one factor two on balanced integer partition and one on residue-coordinate rounding.',
    'The generated splitting degree bound is derived from actual rational coefficient models and the original joint scalar degree bound; the subgroup degree constant depends on the original nilpotence step only.',
    'At all real joint parameters the transformed polynomial evaluates to the genuine native logarithm in the selected subgroup model. The actual original progression parameter remains polynomial after both spatial and progression substitutions.',
    'The finite labels used to thin are the residue vector and quotient coset index, not all geometric interval labels. Varying boxes, frozen observables and tests remain permitted at each retained progression index.',
    'The kernel-label theorem quantifies an explicit predicate of per-index selected witnesses. It proves common labels and actual joint polynomiality, but does not itself construct the entire bad progression family, quantify a common asymptotic subsequence or prove the missing Leibman theorem.',
    'The uniform loss threshold precedes every varying positive t<=2*S and all endpoints, residues and tests. The fixed partition count, rational period and discrepancy constants cannot depend on the progression length.',
    'Paper review covers pinned 06_rough_progressions lines 497-584: native quotient tests, two sampling weights, convex piece selection, fixed residue/coset thinning, exact x=u+Ky sampling and unchanged joint degree/scale growth. The preceding quantitative Leibman input is still unproved.',
    'All retained proof sources and previous transitive axiom sets remain unchanged. Checks are author-side and do not constitute independent kernel replay or a complete proof of the prize target.'
]
src = Path(OLD+'-audit.py').read_text(encoding='utf-8')
src = src.replace("PREFIX = '"+OLD+"'", "PREFIX = '"+PREFIX+"'")
src = src.replace("OLD = 'round-rough-freezing-affine-obstruction'", "OLD = '"+OLD+"'")
start = src.index('MODULES = ')
end = src.index('\ndef declarations():', start)
src = src[:start]+f'MODULES = {MODULES!r}\nCOMPONENTS = {COMPONENTS!r}\nREMAINING = {REMAINING!r}\n'+src[end:]
start = src.index('        application_review=COMPONENTS+')
end = src.index('\n        verified=summary', start)
src = src[:start]+f'        application_review=COMPONENTS+{REVIEW!r}+[REMAINING],'+src[end:]
src = src.replace("reference_scope='06_rough_progressions actual uniformly labelled native kernel quotient tests and simultaneous finite cofinal choice'", "reference_scope='06_rough_progressions actual native discrepancy descent, uniform geometric thresholds and fixed-label joint polynomial reparametrization'")
Path(PREFIX+'-audit.py').write_text(src, encoding='utf-8')
