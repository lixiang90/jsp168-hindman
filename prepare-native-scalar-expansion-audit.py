from pathlib import Path

PREFIX = 'round-rough-native-scalar-expansion'
OLD = 'round-rough-native-complex-descent'
MODULES = ['RoughJointSpatialCoefficients', 'RoughFixedSpatialSupport',
    'RoughJointScalarExpansion', 'RoughNativeScalarExpansion',
    'RoughNativeProjectedObstructionBadFamily']
MODULES = ['Hindman168/'+m+'.lean' for m in MODULES]
COMPONENTS = [
    'RoughJointSpatialCoefficients proves the exact monomial and nested-coefficient connection for optionEquivRight. A nonzero spatial coefficient has parameter natDegree plus spatial degree at most the original joint totalDegree; the zero case is handled with an explicit spatial-degree upper bound.',
    'RoughFixedSpatialSupport constructs a finite positive spatial support depending only on the finite spatial type and q. Membership is exactly positive spatial degree at most q; zero is excluded, and the spatial support of every joint polynomial of totalDegree at most q lies in this support together with zero.',
    'RoughJointScalarExpansion proves exact algebraic expansion of every joint scalar polynomial into a separate constant coefficient and coefficient polynomials on the fixed spatial support, with all weighted degree bounds. Projection of an actual vector polynomial by any real linear functional therefore has this fixed-support expansion at every real coordinate.',
    'RoughNativeScalarExpansion constructs the scalar polynomial representation of the actual native logarithm character from its given joint vector logarithm polynomial. It also proves equality of the raw scalar spatial projection at every real parameter with the finite coefficient expansion, retaining the original degree bound.',
    'RoughNativeProjectedObstructionBadFamily removes the caller-supplied scalar representation, support, constant polynomial and weighted coefficient-degree premises from the complex obstruction descent entry. Actual affine obstructions are stated directly for the scalar projection of the given native logarithm polynomial; the theorem constructs a strictly smaller native real bad family at discrepancy eta/4.'
]
REMAINING = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'The actual native logarithm polynomial now supplies the character scalar representation, fixed positive spatial support and all weighted coefficient-degree bounds. Actual affine obstructions stated directly on its raw scalar projection, with original complex tests, yield smaller native real bad families after the proved interpolation, fractional thinning, arithmetic and geometric descent. '
    'The quantitative Leibman obstruction and its uniform finite nonzero character list must still produce these affine obstructions, including corrected arbitrary-box comparison and stretched-filtration applicability. '
    'Connect finite character selection and rational direction/period selection to this entry and finish dimension induction using actual length restriction, cofinal scale subsequences and the zero-dimensional base. '
    'Finite density extraction from exceptional sets and the full uniform rough-step comparison remain open. '
    'Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
REVIEW = [
    'optionEquivRight separates the progression variable into the coefficient ring of real univariate polynomials. The nested coefficient equals the original coefficient at I.optionElim n; this is a proved algebraic identity, not a sampled representation premise.',
    'Weighted degree for a nonzero coefficient uses its actual nonzero leading coefficient and original monomial support. For a zero coefficient, natDegree is zero, so the spatial-degree <= q premise is necessary and explicitly retained in the general lemma.',
    'The fixed finite support includes every positive multiindex of spatial degree <= q, even those with zero coefficients. It depends only on q and the finite spatial type, not on character, coefficients, source length, boxes, scale or tests. The constant multiindex is excluded and handled separately.',
    'The q=0 and empty spatial-type cases are covered by the same definitions and proofs. No nonexistent positive-degree coefficient is introduced to force a nonempty support.',
    'Scalar expansion is equality of actual multivariate polynomials, with all-real evaluation identities. It does not infer polynomial equality merely from finitely many integer sample values.',
    'Native scalar expansion uses the original global logarithm and original linear character. The joint vector degree and exact native logarithm identity remain explicit, while scalar expansion and weighted degrees are constructed.',
    'The raw scalar spatial projection is defined by projecting the given vector polynomial, applying optionEquivRight and evaluating the coefficient polynomials at the real progression parameter. Its equality with the finite spatial expansion is proved for every real parameter before affine coefficient extraction.',
    'The projected-obstruction entry selects partition count and output Lipschitz bound before target length and its source length before the varying actual polynomial data. No varying-support dependence is hidden in these uniform choices.',
    'The theorem still requires a rational horizontal character and rational direction with a positive lattice period, original complex discrepancies and actual affine coefficient obstructions. It does not prove quantitative Leibman, its finite character list, or the dimension-induction contradiction.',
    'Paper comparison covers equation rough-character-polynomial and rough-substituted-obstruction, fixed coefficient and degree bounds, the constant-term split, and the final smaller-family construction. All six pinned primary sections are checked against fixed Git content.',
    'All retained proof sources and transitive axiom sets are unchanged; fresh focused checks, full build and selected axiom reports are author-side verification with standard axioms only.'
]
src = Path(OLD+'-audit.py').read_text(encoding='utf-8')
src = src.replace("PREFIX = '"+OLD+"'", "PREFIX = '"+PREFIX+"'")
src = src.replace("OLD = 'round-rough-native-obstruction-descent'", "OLD = '"+OLD+"'")
start = src.index('MODULES = ')
end = src.index('\ndef declarations():', start)
src = src[:start]+f'MODULES = {MODULES!r}\nCOMPONENTS = {COMPONENTS!r}\nREMAINING = {REMAINING!r}\n'+src[end:]
start = src.index('        application_review=COMPONENTS+')
end = src.index('\n        verified=summary', start)
src = src[:start]+f'        application_review=COMPONENTS+{REVIEW!r}+[REMAINING],'+src[end:]
src = src.replace("reference_scope='06_rough_progressions complex-observable bad families and actual obstruction descent with explicit component reduction'", "reference_scope='06_rough_progressions fixed character scalar expansion, weighted degrees and actual projected coefficient obstruction descent'")
Path(PREFIX+'-audit.py').write_text(src, encoding='utf-8')
