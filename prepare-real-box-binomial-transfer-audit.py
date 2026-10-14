from pathlib import Path

PREFIX = 'round-rough-real-box-binomial-transfer'
OLD = 'round-rough-equal-cube-box-transfer'
MODULES = ['Hindman168/'+m+'.lean' for m in
    ['RoughRealBoxCeil', 'RoughCorrectedRealBoxCubeSelection', 'RoughNativeRealBoxBinomialTransfer']]
COMPONENTS = [
    'RoughRealBoxCeil defines the actual integer samples of a half-open real box and their natural ceil-endpoint widths. It proves the exact real-inequality membership criterion, equality to the corresponding integer width box and uniform lower width and endpoint location bounds.',
    'RoughCorrectedRealBoxCubeSelection assembles actual equal-side cube selection for half-open real boxes. After choosing the ratio and threshold before all varying endpoints and observables, it supplies a positive fixed-ratio side, bounded signed origin, actual sample containment and at least half the original Haar discrepancy.',
    'RoughNativeRealBoxBinomialTransfer upgrades the conditional native finite character transfer to actual integer samples of half-open real boxes, with a positive uniform coefficient budget fixed before varying source data. The selected index remains in the supplied finite set and all positive scalar coefficients of the actual integer-multiplied projection are bounded.'
]
REMAINING = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'The geometric and algebraic corrected box consequence is now assembled for actual integer samples of half-open real boxes, including exact ceil endpoint representation, count and location budgets, actual equal-cube tiling and selection, fixed floor side, finite character index retention and native binomial-to-monomial transfer. '
    'The transfer remains conditional on exact equal-cube binomial character obstruction; it does not prove quantitative Leibman or construct a uniformly finite nonzero horizontal character list. '
    'Prove the equal-side quantitative Leibman input and its finite character construction. Group difference translation is proved; actual native logarithm polynomials still need the stretched lower-central filtration and actual BCH coefficient/difference membership. Existing nativeGroupLowerCentralSeries_eq_exponential and nativeLieLowerCentralSubgroup normality/closedness/contractibility can be reused when constructing the stretched family. '
    'Connect the resulting finite character selection to normalized descent and finish dimension induction using actual length restriction, cofinal scales and the zero-dimensional base. '
    'Finite density extraction from exceptional sets and the full uniform rough-step comparison remain open. '
    'Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
REVIEW = [
    'The real box is explicitly half-open in each coordinate: lo <= integer point < hi. Its membership is exactly the integer interval between the two ceil endpoints. Other endpoint conventions are not silently asserted.',
    'Real side lengths at least c*Z with c*Z >= 2 give integer sample widths at least (c/2)*Z. The ceiling difference is nonnegative and is identified exactly with the cast of its natural toNat width; this is proved before applying integer cube geometry.',
    'The upper ceil endpoint may exceed the real upper endpoint by less than one. With Z >= 1, uniform location bounds are absorbed by C+1. All inverse translation constants remain independent of variable endpoints and polynomial coefficients.',
    'The real-box threshold is the maximum of the fixed integer-box threshold and 2/c. It is selected before all real endpoints, scales, vector polynomials, scalar parameter values and test observables.',
    'The actual selected cube points are transported through equality of finite point sets. Haar discrepancy and finite mean normalization are preserved by that equality; no sample-set approximation or additional averaging error is introduced.',
    'Native transfer uses the already proved actual integer cube selection and coefficient conversion with fixed parameters c/2 and C+1. Its output remains a member of the same supplied finite character index set.',
    'The equal-cube analytic premise still supplies both exact translated binomial polynomial equality and its modular coefficient bounds. These hypotheses remain explicit and unproved. They are not axioms or consequences of the geometric selection theorem.',
    'Existing exact native group/Lie lower-central equality is available in NativeGroupLowerCentralExact. The connected contractible exponential Lie subgroups are available in NativeLieLowerCentralSubgroups. These existing proofs are not yet the missing stretched-filtration weighted BCH coefficient argument.',
    'Paper comparison covers the corrected rough-progression box statement and its fixed count and location budgets. All six pinned primary sections, retained source hashes and transitive axiom sets are checked before recording progress.',
    'Focused autoImplicit=false checks, full build and standard-only selected axiom reports are author-side verification; no independent replay, completed StrongConjecture or prize eligibility is claimed.'
]
src = Path(OLD+'-audit.py').read_text(encoding='utf-8')
src = src.replace("PREFIX = '"+OLD+"'", "PREFIX = '"+PREFIX+"'")
src = src.replace("OLD = 'round-rough-cube-selection-start'", "OLD = '"+OLD+"'")
start = src.index('MODULES = ')
end = src.index('\ndef declarations():', start)
src = src[:start]+f'MODULES = {MODULES!r}\nCOMPONENTS = {COMPONENTS!r}\nREMAINING = {REMAINING!r}\n'+src[end:]
start = src.index('        application_review=COMPONENTS+')
end = src.index('\n        verified=summary', start)
src = src[:start]+f'        application_review=COMPONENTS+{REVIEW!r}+[REMAINING],'+src[end:]
src = src.replace("reference_scope='06_rough_progressions actual multivariate equal-cube box consequence, conditional native coefficient transfer and group difference translation'", "reference_scope='06_rough_progressions exact half-open real-box integer samples, ceil count/location budgets and conditional native finite character transfer'")
Path(PREFIX+'-audit.py').write_text(src, encoding='utf-8')
