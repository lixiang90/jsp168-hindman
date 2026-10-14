from pathlib import Path
import re

PREFIX = 'round-rough-character-grid-uniform-degree'
OLD = 'round-rough-native-filtered-polynomial'
MODULES = ['Hindman168/'+m+'.lean' for m in [
    'RoughNativeStretchedLieTerminal', 'RoughVectorZeroTrim',
    'RoughNativeUniformDifferenceDegree', 'RoughFiniteFunctionalGrid',
    'RoughNativeCharacterBasisMultipliers', 'RoughNativeFiniteFunctionalGrid',
    'RoughNativeFunctionalGridBudget', 'RoughNativeHorizontalCharacterGrid',
    'RoughNativeHorizontalGridNormalization', 'RoughNativeRealBoxHorizontalTransfer']]
COMPONENTS = [
    'Actual stretched native Lie layers terminate at s*D+1 and thereafter for original group step at most s. Removing zero vector terms preserves exact evaluation and weighted membership and bounds remaining ordinary degree by s*D-k.',
    'Every actual k-fold native group difference has an actual logarithm vector polynomial representation with degree at most s*D-k, uniformly over all shift lists and coefficients. For k>s*D the original group difference is exactly one.',
    'A constructive finite grid of real linear functionals on a fixed finite basis is enumerated by bounded integer values on prescribed positive multiples of the basis vectors. Every integral bounded evaluation functional belongs to this grid, with a cardinality bound by the actual finite integer box.',
    'Actual original lattice rational basis vectors have fixed positive integer multiples whose original exponentials lie in Gamma. These actual lattice sampling vectors are selected from proved positive powers in the original rational log span, not from an assumed additive Log Gamma lattice.',
    'A fixed positive norm budget for the actual lattice sampling vectors turns a fixed operator norm bound on a Gamma-integral functional into membership in a fixed finite grid. The grid and ceiling budget are selected before every varying functional or polynomial.',
    'The finite grid is filtered to actual nonzero horizontal Gamma-integral functionals. Every remaining entry defines an actual continuous additive and surjective real character on the original group. Original native bracket annihilation and integrality suffice for norm-bounded input membership.',
    'Every candidate in the fixed finite horizontal grid has a rational normalized direction with character value one and a positive original lattice period. Direction and period functions for the entire finite subtype are chosen before varying source data.',
    'The actual corrected half-open real-box coefficient transfer now constructs its own fixed finite horizontal candidate grid from a norm budget and an existential equal-cube obstruction premise. It retains actual character membership and all positive original multiplied scalar coefficient bounds, with uniform constants before source variables.'
]
REMAINING = (
    'StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'The corrected real-box geometric and coefficient transfer, actual rational connected stretched filtration, '
    'native weighted Picard/BCH group difference polynomiality and uniform ordinary difference degree are proved. '
    'Fixed finite nonzero horizontal character candidates, actual normalized rational directions and positive lattice periods '
    'are constructed from a fixed operator norm budget. The real-box transfer is still conditional on equal-cube exact '
    'binomial obstruction existence and its modular coefficient bounds. '
    'Prove the actual equal-side quantitative Leibman input and adapted rational basis; in particular prove character '
    'existence and the uniform size bound and connect the paper Malcev-coordinate size to the fixed functional norm budget. '
    'No quantitative equidistribution theorem is asserted by the finite grid construction. '
    'Connect the actual finite candidate obstruction to normalized descent and finish dimension induction with actual '
    'length restriction, cofinal scales and the zero-dimensional base. Finite density extraction and the full uniform '
    'rough-step comparison remain open. Conditional face laws, buffered short-bin geometry, prior-event positivity, '
    'extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability '
    'Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved '
    'existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
REVIEW = [
    'The vector trim deletes exactly zero vector coefficients, rather than zero scalar polynomials. Exact evaluation and weighted membership are preserved. Beyond-terminal weighted membership forces a nonzero vector term to have totalDegree+k <= s*D, even for k greater than s*D.',
    'The uniform degree is s*D-k with natural subtraction. For k>s*D all actual group differences are one; no assertion that natural degree of a zero polynomial is negative is made.',
    'The finite functional grid enumerates integer evaluations divided by fixed positive basis multipliers. Basis extensionality proves full functional equality, not merely agreement on the finitely many tested points.',
    'Original lattice basis vectors lie in the actual rational log span. The original positive-power theorem and genuine exponential natural-scaling law supply lattice points. Log Gamma is never assumed to be an additive lattice.',
    'The norm budget is one plus the finite sum of actual sampling-vector norms and is positive even when the model is zero-dimensional. Ceiling conversion is valid for every nonnegative operator norm budget. Empty candidate grids do not imply existence of a nonzero character.',
    'The horizontal filter requires nonzero differential, annihilation of the original actual commutator layer and Gamma-integral original logarithm values. Actual character continuity, additivity, surjectivity and lattice integrality are proved for every selected entry.',
    'Normalization uses a rational basis value where the nonzero functional does not vanish, scales in the original rational log span and uses the original positive-power criterion. All finite-subtype direction and period choices are independent of varying source variables.',
    'The real-box theorem keeps the equal-cube existence premise explicit, including exact translated binomial polynomial equality and modular coefficients. It replaces a supplied finite index list by a proved candidate grid; it does not discharge quantitative Leibman.',
    'Operator norm bounds are not silently identified with the paper integer coefficient-vector size in an adapted Malcev basis. That basis construction, size conversion and the actual quantitative existence theorem remain open.',
    'Focused autoImplicit=false checks, full build, retained proof hashes and standard-only selected axiom reports are author-side verification. All six pinned primary sections are compared; no independent replay, full target or prize eligibility is claimed.'
]
src = Path(OLD+'-audit.py').read_text(encoding='utf-8')
src = re.sub(r'^PREFIX = .*?$', 'PREFIX = '+repr(PREFIX), src, count=1, flags=re.M)
src = re.sub(r'^OLD = .*?$', 'OLD = '+repr(OLD), src, count=1, flags=re.M)
start = src.index('MODULES = ')
end = src.index('\ndef declarations():', start)
src = src[:start]+f'MODULES = {MODULES!r}\nCOMPONENTS = {COMPONENTS!r}\nREMAINING = {REMAINING!r}\n'+src[end:]
start = src.index('        application_review=COMPONENTS+')
end = src.index('\n        verified=summary', start)
src = src[:start]+f'        application_review=COMPONENTS+{REVIEW!r}+[REMAINING],'+src[end:]
src = re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions uniform group-difference degree and actual finite horizontal character grids, directions and lattice periods; quantitative existence remains open'", src)
Path(PREFIX+'-audit.py').write_text(src, encoding='utf-8')
