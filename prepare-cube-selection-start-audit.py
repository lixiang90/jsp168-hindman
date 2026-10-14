from pathlib import Path

PREFIX = 'round-rough-cube-selection-start'
OLD = 'round-rough-binomial-obstruction-transfer'
MODULES = ['Hindman168/'+m+'.lean' for m in
    ['RoughComplexFiberMean', 'RoughEqualIntervalTiling', 'RoughComplexBoundarySelection']]
COMPONENTS = [
    'RoughComplexFiberMean proves the exact complex mean decomposition into finite label fibers with weights equal to their cardinality divided by total cardinality. From a nonempty sampled set it selects a nonempty actual fiber with at least the original Haar discrepancy, without a component-count loss.',
    'RoughEqualIntervalTiling constructs equal-side integer interval tiles for signed origins and arbitrary natural widths. It proves containment, exact tile cardinality, quotient-remainder coordinates for every point in the tiled region and exact omitted boundary cardinality width modulo N.',
    'RoughComplexBoundarySelection connects bounded-observable boundary trimming to actual nonempty fiber discrepancy selection. If omitted points are fewer than all original points and their normalized contribution is at most delta, a nonempty retained fiber has Haar discrepancy at least eta minus delta.'
]
REMAINING = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'Exact complex finite fiber averaging and discrepancy selection are proved, as is boundary-trimmed fiber selection under an explicit cardinality and error budget. Actual one-dimensional equal interval tiling and its exact boundary cardinality are proved. '
    'Still assemble the multivariate integer equal-cube grid, identify its actual label fibers, bound the product-box boundary fraction, choose the fixed small cube scale and connect cube-origin bounds and filtered polynomial translation. '
    'The algebraic transfer from an exact binomial cube obstruction to ordinary coefficients of the actual multiplied native scalar projection is proved; exact binomial representation and modular obstruction remain inputs. '
    'Prove the equal-side quantitative Leibman input, a uniform finite nonzero horizontal character list and stretched-filtration applicability; assemble the corrected arbitrary-box obstruction. '
    'Connect finite character selection to normalized descent and finish dimension induction using actual length restriction, cofinal scales and the zero-dimensional base. '
    'Finite density extraction from exceptional sets and the full uniform rough-step comparison remain open. '
    'Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
REVIEW = [
    'Finite fiber averaging uses the actual complex set mean and actual cardinality weights. Its identity also covers empty fibers and an empty whole set, since multiplying an empty fiber mean by its zero cardinality gives its zero sum.',
    'Haar discrepancy selection requires a nonempty whole set. Nonnegative weights sum to one by the existing proved uniform fiber mass identity, and convex selection returns strictly positive weight, which implies an actual nonempty fiber.',
    'The interval tiling origin is an arbitrary integer, so negative origins are covered. The retained length is N*(width/N) and the omitted length is width modulo N, using exact natural quotient-remainder arithmetic.',
    'Each full interval tile has cardinality N, and all such tiles stay inside the original interval. Coordinate decomposition requires N > 0 and provides actual r < width/N and v < N for every retained integer point.',
    'The interval cardinality and boundary identity are proved even for zero width or zero N; no division by a real length or positivity is hidden there. Multi-dimensional cube disjointness, product-grid labels and boundary fraction estimates are not asserted by these one-dimensional results.',
    'Boundary selection requires T subset S and discarded cardinality strictly below S.card. These ensure retained nonemptiness. The separate boundary error inequality uses 2*B*discarded/S.card and a globally bounded complex observable. Its proof handles normalization change in the set mean.',
    'The selected discrepancy is eta minus delta. A positive fixed eta and a suitably small delta, and the integer geometric estimate producing that delta, are still needed when applying this lemma to the corrected box proof.',
    'Paper comparison concerns the cube-tiling boundary trimming and convex Haar selection steps in the pinned rough-progressions section. Equal-side quantitative Leibman and stretched-filtration applicability remain explicit missing proofs.',
    'All retained proof source hashes and transitive axiom sets are unchanged. Focused autoImplicit=false checks, full build, standard-only selected axiom reports and all six pinned primary paper sections are checked before recording progress.'
]
src = Path(OLD+'-audit.py').read_text(encoding='utf-8')
src = src.replace("PREFIX = '"+OLD+"'", "PREFIX = '"+PREFIX+"'")
src = src.replace("OLD = 'round-rough-box-character-translation'", "OLD = '"+OLD+"'")
start = src.index('MODULES = ')
end = src.index('\ndef declarations():', start)
src = src[:start]+f'MODULES = {MODULES!r}\nCOMPONENTS = {COMPONENTS!r}\nREMAINING = {REMAINING!r}\n'+src[end:]
start = src.index('        application_review=COMPONENTS+')
end = src.index('\n        verified=summary', start)
src = src[:start]+f'        application_review=COMPONENTS+{REVIEW!r}+[REMAINING],'+src[end:]
src = src.replace("reference_scope='06_rough_progressions exact binomial denominator clearing, uniform coefficient budget, cube-scale inverse translation and native character multiplication'", "reference_scope='06_rough_progressions actual complex fiber averaging, one-dimensional equal interval tiling and boundary Haar selection'")
Path(PREFIX+'-audit.py').write_text(src, encoding='utf-8')
