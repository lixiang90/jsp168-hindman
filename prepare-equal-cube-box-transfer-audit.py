from pathlib import Path

PREFIX = 'round-rough-equal-cube-box-transfer'
OLD = 'round-rough-cube-selection-start'
MODULES = ['Hindman168/'+m+'.lean' for m in [
    'RoughEqualIntervalCoordinates', 'RoughEqualCubeDefinitions', 'RoughEqualCubeFibers',
    'RoughEqualTiledBoxGeometry', 'RoughProductBoundaryFraction',
    'RoughEqualBoxBoundaryFraction', 'RoughEqualBoxBoundaryScale', 'RoughEqualCubeSampling',
    'RoughEqualCubeHaarSelection', 'RoughEqualCubeSideFloor', 'RoughEqualCubeOriginBounds',
    'RoughEqualCubeRatioChoice', 'RoughCorrectedBoxCubeSelection',
    'RoughNativeBoxBinomialTransfer', 'RoughFilteredPolynomialTranslation']]
COMPONENTS = [
    'RoughEqualIntervalCoordinates proves exact quotient labels for full integer interval tiles, the equivalence between a retained point with a specified quotient and membership in its actual tile, and local coordinates in range N for every tile point.',
    'RoughEqualCubeDefinitions defines actual finite integer boxes by signed origin and natural widths, their retained equal-cube region, equal cube origins, actual cubes and finite dependent quotient labels. It proves the equal interval product representation and exact box and cube cardinalities.',
    'RoughEqualCubeFibers proves that every actual retained point has its natural quotient label and that each label fiber equals the specified actual equal-side cube. Every full cube lies inside the original width box.',
    'RoughEqualTiledBoxGeometry proves actual retained-region containment and nonemptiness when N > 0 and N fits every width, exact product cardinality of that region, and nonemptiness of all full cubes.',
    'RoughProductBoundaryFraction proves the finite product deficit inequality for factors in [0,1], used to bound the total omitted fraction by the sum of individual coordinate deficits.',
    'RoughEqualBoxBoundaryFraction proves the actual omitted integer-box cardinality divided by original cardinality is at most the sum of coordinate remainder ratios, and at most the sum of N divided by coordinate widths.',
    'RoughEqualBoxBoundaryScale converts the actual boundary fraction to (number of variables)*lam/c when every integer width is at least c*Z and the cube side is at most lam*Z.',
    'RoughEqualCubeSampling proves injection of local natural cube coordinates, equality of the actual cube to their translated image, and equality of its complex mean to the equal-side range-N sample mean.',
    'RoughEqualCubeHaarSelection selects an actual cube with equal-side range-N sample discrepancy at least eta minus delta after trimming a boundary with error budget delta. Label fibers are actual cubes, not assumed components.',
    'RoughEqualCubeSideFloor proves positivity and fixed-ratio lower and upper bounds for the actual natural floor cube side once lam*Z >= 2, and proves that this side fits every integer width when lam <= c.',
    'RoughEqualCubeOriginBounds proves the actual cube origin belongs to its cube and derives its coordinate absolute bound C*Z from original box endpoint bounds, including negative origins.',
    'RoughEqualCubeRatioChoice constructs one fixed positive ratio <= min(1,c) whose boundary contribution 2*B*(number of variables)*lam/c is at most eta/4. It handles B = 0 and a zero-dimensional spatial type using B+1 and dimension+1 in its denominator.',
    'RoughCorrectedBoxCubeSelection assembles the actual integer equal-cube selection. It chooses lam and Z0 before all varying boxes, observables and means; outputs a positive side N between lam*Z/2 and lam*Z, a bounded signed origin, actual sampled-point containment and at least eta/2 Haar discrepancy.',
    'RoughNativeBoxBinomialTransfer combines this actual cube selection with the proved integer binomial coefficient transfer into a uniform positive ordinary monomial obstruction budget on the actual multiplied native scalar projection. Character indices remain in the supplied finite set. Exact equal-cube binomial character obstruction is still an explicit premise.',
    'RoughFilteredPolynomialTranslation defines actual left group differences and their iterates, proves they commute exactly with additive-domain translation, and proves preservation of prescribed subgroup-valued polynomiality under translation. It also proves that a zero step gives the identity group element.'
]
REMAINING = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'Actual multivariate equal-cube geometry for integer width boxes, exact finite quotient-label fibers, sample-mean equality, boundary fraction, fixed small floor side, bounded signed origin and Haar discrepancy selection are proved. '
    'The conditional native box transfer now assembles this geometry and all coefficient conversions with character indices in a supplied finite set. The equal-cube binomial obstruction premise is not proved; it still contains the essential quantitative Leibman character existence input. '
    'Connect general real-box endpoints to the integer width representation with uniform count and location bounds where needed. '
    'Prove the equal-side quantitative Leibman theorem and construction of its uniformly finite nonzero horizontal character list. Group difference translation is proved, but the actual native logarithm polynomial still needs the stretched lower-central filtration, its rational connected subgroup properties and BCH coefficient/difference membership proof. '
    'Connect the resulting finite character selection to normalized descent and finish dimension induction using actual length restriction, cofinal scales and the zero-dimensional base. '
    'Finite density extraction from exceptional sets and the full uniform rough-step comparison remain open. '
    'Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
REVIEW = [
    'The definitions describe actual finite integer point sets. Quotient-label types are finite dependent functions with each coordinate in Fin(width/N). The default label outside the retained region is zero, whose admissibility is derived from N <= width and N > 0; all retained points use their true quotient.',
    'The label fiber equality is proved from quotient-remainder arithmetic in each coordinate. No cube partition, local-coordinate bijection or convex mixture identity is an additional assumption of corrected cube selection.',
    'All coordinates may have signed integer origins and unequal original widths. Only the selected full cube has equal side N in every coordinate. The proof does not invoke an unrestricted unequal-side quantitative equidistribution theorem.',
    'The boundary fraction is the actual discarded cardinality divided by the positive original box cardinality. The proof casts the exact cardinal subtraction using actual containment, identifies the retained-to-original product ratio and applies the proved finite product deficit inequality.',
    'The boundary bound first retains exact coordinate remainders and then bounds each remainder by N. Integer widths of at least c*Z and N <= lam*Z yield the uniform dimension*lam/c bound. No independence or probabilistic boundary approximation is assumed.',
    'Complex boundary trimming controls normalization of the mean by 2*B times the discarded fraction. Nonempty retained cubes are proved before finite convex discrepancy selection. The selected discrepancy has no loss depending on the number of cubes.',
    'Finite operations sometimes infer distinct decidability instances for the function type. They are transported by subsingleton equality of decision procedures; no new typeclass instance, unsafe code or computational proof oracle is introduced.',
    'The actual cube side is the natural floor of lam*Z. Z0 >= max(1,2/lam) guarantees positive N and N >= lam*Z/2. Taking lam <= c makes N fit every coordinate width. lam and Z0 are selected before variable source data.',
    'The fixed ratio is positive even when B = 0 or the spatial type is empty. B+1 and dimension+1 avoid zero denominators; min with one and c yields all required size bounds. Cube and sample identities also handle the empty spatial type.',
    'The origin bound is derived by membership of the actual cube origin in the original box and its endpoint location bounds. It therefore supplies precisely the bounded integer translation required in the coefficient comparison.',
    'The native transfer retains an explicit finite index set s: the analytic cube premise must return i in s, and the resulting ordinary monomial obstruction has i in the same s. The integer multiplier preserves actual projection identity and earlier lattice integrality results; no existence or bounded-height theorem for characters is inferred.',
    'The final native transfer has a uniform positive output budget max(1,budget), chosen before all source boxes, vector logarithm polynomials, parameter values, observables and means. Positive spatial coefficients of every degree are covered by the preceding actual total-degree proof.',
    'The analytic premise supplies both equality of the actual translated real binomial polynomial and coefficient modular estimates on the equal cube. Its existence is not asserted, and it has not been added as an axiom. Completion of this conditional transfer is not completion of quantitative Leibman or StrongConjecture.',
    'Group differences use P(x+h)*P(x)^(-1), matching the pinned rough-progressions section. Iterated differences range over all finite step lists and retain their length. Translation preservation is proved for an arbitrary prescribed subgroup family; this alone does not prove that the family is the rational connected stretched lower-central filtration or that actual logarithm polynomials satisfy the membership predicate.',
    'Paper comparison covers actual equal-side cube tiling, omitted strips, complex convex Haar selection, bounded cube location, uniform coefficient conversion and preservation of group polynomiality under integer translation. All six pinned primary sections are checked against fixed Git content.',
    'All retained proof source hashes and transitive axiom sets are unchanged. Focused autoImplicit=false checks, full build, standard-only selected axiom reports and pinned primary source checks are author-side verification, not independent kernel replay.'
]
src = Path(OLD+'-audit.py').read_text(encoding='utf-8')
src = src.replace("PREFIX = '"+OLD+"'", "PREFIX = '"+PREFIX+"'")
src = src.replace("OLD = 'round-rough-binomial-obstruction-transfer'", "OLD = '"+OLD+"'")
start = src.index('MODULES = ')
end = src.index('\ndef declarations():', start)
src = src[:start]+f'MODULES = {MODULES!r}\nCOMPONENTS = {COMPONENTS!r}\nREMAINING = {REMAINING!r}\n'+src[end:]
start = src.index('        application_review=COMPONENTS+')
end = src.index('\n        verified=summary', start)
src = src[:start]+f'        application_review=COMPONENTS+{REVIEW!r}+[REMAINING],'+src[end:]
src = src.replace("reference_scope='06_rough_progressions actual complex fiber averaging, one-dimensional equal interval tiling and boundary Haar selection'", "reference_scope='06_rough_progressions actual multivariate equal-cube box consequence, conditional native coefficient transfer and group difference translation'")
Path(PREFIX+'-audit.py').write_text(src, encoding='utf-8')
