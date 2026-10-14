from pathlib import Path

PREFIX = 'round-rough-box-character-translation'
OLD = 'round-rough-native-scalar-expansion'
MODULES = ['RoughNativeNormalizedObstructionBadFamily', 'RoughNativeFiniteBadData',
    'RoughModOneIntegerCombination', 'RoughSignedTranslationCoefficients',
    'RoughIntegerTranslationInverse', 'RoughBoxCharacterTranslation',
    'RoughBoxCharacterFixedSupport', 'RoughComplexHaarObstruction']
MODULES = ['Hindman168/'+m+'.lean' for m in MODULES]
COMPONENTS = [
    'RoughNativeNormalizedObstructionBadFamily constructs the rational normalized direction and positive actual lattice period from a lattice-integral character nonzero on the specified rational Lie subalgebra, and connects these data to projected-obstruction descent. The direction and period are selected before all target lengths and varying source data.',
    'RoughNativeFiniteBadData selects one fixed smaller native quotient and its own fixed degree, box, test, discrepancy and rescaling constants from finite cofinal choices. It constructs lengthwise strictly increasing scale subsequences preserving scale divergence and power domination, allowing different original finite choices to have different periods and bounds.',
    'RoughModOneIntegerCombination bounds the modulo-one norm of a finite integer linear combination by the absolute integer coefficients times the individual modulo-one norms. It constructs one actual nearby integer using rounded summands.',
    'RoughSignedTranslationCoefficients gives exact signed integer binomial weights for every positive coefficient after integer translation, proves vanishing outside coordinatewise domination, and bounds their absolute values uniformly by degree and translation size. Negative cube-origin translations are covered.',
    'RoughIntegerTranslationInverse proves exact inverse affine translation of actual multivariate polynomials over commutative rings and preservation of totalDegree.',
    'RoughBoxCharacterTranslation proves that integer translation transfers positive-degree coefficient modulo-one bounds with errors A*Z^(-degree) to bounds with the same scale exponent and a constant uniform in all scalar coefficients.',
    'RoughBoxCharacterFixedSupport constructs the fixed positive spatial expansion of every polynomial of degree at most q, replacing coefficient-dependent support counts by a support depending only on q and the finite spatial type. It proves the uniform translation bound and the inverse translation from a cube polynomial back to the original polynomial.',
    'RoughComplexHaarObstruction proves that at least one of two sample means has half their mutual discrepancy against any fixed Haar mean, transports discrepancy across a bounded perturbation, and selects a positive-weight component of a finite convex combination with at least the full mean discrepancy. There is no discrepancy loss by component count.'
]
REMAINING = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'Character normalization is now connected to the actual projected obstruction constructor, and finite smaller quotients may have different fixed periods and quantitative bounds while retaining lengthwise cofinal subsequences. '
    'The corrected box consequence now has a proved signed integer inverse-translation coefficient estimate with fixed degree support and coefficient-independent constants. Haar sample splitting, perturbation and convex selection are proved for complex means. '
    'Still prove the equal-side quantitative Leibman input, binomial-to-ordinary coefficient denominator clearing, actual integer equal-cube tiling with boundary fraction estimates, finite horizontal character list and stretched-filtration applicability; assemble these into the corrected arbitrary-box obstruction. '
    'Connect finite character selection to normalized descent and finish dimension induction using actual length restriction, cofinal scales and the zero-dimensional base. '
    'Finite density extraction from exceptional sets and the full uniform rough-step comparison remain open. '
    'Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
REVIEW = [
    'The normalized direction and positive period are derived from the existing proved rational lattice pivot and rational-power membership results. The character is still required to be integral on the actual lattice, kill brackets on the specified subgroup, and be nonzero there; existence of a quantitative obstructing character is not asserted.',
    'Finite cofinal selection uses actual length restriction before constructing a strictly increasing subsequence at each prescribed length. Selecting only a quotient occurring at unbounded lengths would be insufficient; the theorem retains scale cofinality and its selected index-specific period and all bounds.',
    'Modulo-one linear combinations use integer weights, so rounded coefficient parts contribute an integer exactly. Real weights would invalidate this step and are not permitted.',
    'Signed binomial translation weights are actual integers even for negative cube origins. Coefficients vanish unless the original multiindex dominates the output multiindex coordinatewise. The separate spatially constant coefficient contributes nothing to positive-degree outputs.',
    'Translation cancellation uses Z > 0: powers Z^(degree difference) from cube location cancel the higher-degree errors Z^(-original degree). The remaining exponent is the output degree. The factor max(1,C)^q controls all bounded translation powers, including C below one.',
    'The generic support-count estimate is upgraded to the fixed set of all positive multiindices of degree <= q. Thus the resulting constant depends only on spatial type, q, C and A; it is independent of polynomial coefficients, cube size, source progression length and the actual support of the polynomial.',
    'The inverse translation is equality of actual polynomials, proved by ring-homomorphism extensionality on constants and variables. Total degree is preserved by the inverse and the forward degree bounds, not merely bounded at sampled points.',
    'Haar mean lemmas take an arbitrary complex center and do not assume or construct a Haar probability measure. Convex selection requires nonnegative weights with total one and returns an index with strictly positive weight. These lemmas alone do not supply the missing integer cube geometry or analytic input.',
    'The binomial-to-monomial denominator clearing from the equal-cube statement has not yet been proved. Ordinary monomial modular bounds are explicit premises of translation; no analytic or binomial obstruction is silently assumed as a conclusion.',
    'The next denominator work can use the installed mathlib descPochhammer polynomials, map identities, degree, and product-range evaluation. The fixed multiplier in the pinned paper is (q!)^(number of spatial variables).',
    'Paper comparison covers the corrected box derivation, bounded-location inverse translation, sample-versus-Haar split, finite group selection and fixed character normalization. All six pinned primary sections are checked against fixed Git content.',
    'All retained proof sources and transitive axiom sets are unchanged; focused checks, full build, selected standard-only axiom reports and primary-source checks are author-side verification.'
]
src = Path(OLD+'-audit.py').read_text(encoding='utf-8')
src = src.replace("PREFIX = '"+OLD+"'", "PREFIX = '"+PREFIX+"'")
src = src.replace("OLD = 'round-rough-native-complex-descent'", "OLD = '"+OLD+"'")
start = src.index('MODULES = ')
end = src.index('\ndef declarations():', start)
src = src[:start]+f'MODULES = {MODULES!r}\nCOMPONENTS = {COMPONENTS!r}\nREMAINING = {REMAINING!r}\n'+src[end:]
start = src.index('        application_review=COMPONENTS+')
end = src.index('\n        verified=summary', start)
src = src[:start]+f'        application_review=COMPONENTS+{REVIEW!r}+[REMAINING],'+src[end:]
src = src.replace("reference_scope='06_rough_progressions fixed character scalar expansion, weighted degrees and actual projected coefficient obstruction descent'", "reference_scope='06_rough_progressions normalized character descent, finite varying bad data and signed inverse translation in corrected box consequence'")
Path(PREFIX+'-audit.py').write_text(src, encoding='utf-8')
