from pathlib import Path

PREFIX = 'round-rough-native-bad-family'
OLD = 'round-rough-native-piece-descent'
MODULES = ['RoughNativeBadIndex', 'RoughNativeModelBadIndex',
    'RoughNativeBadProgressionThinning', 'RoughCofinalSubsequences',
    'RoughNativeBadFamily', 'RoughNativeSmallerBadFamily',
    'RoughNativeModelBadFamily', 'RoughNativeZeroDimension']
MODULES = ['Hindman168/'+m+'.lean' for m in MODULES]
COMPONENTS = [
    'RoughNativeBadIndex defines an actual discrepant pair of nonempty finite box samples on the specified native quotient, with uniformly bounded Lipschitz real observable and both endpoint bounds. Upper-bound relaxation and exact progression reparametrization are proved.',
    'RoughNativeModelBadIndex constructs these actual bad-index witnesses from the original coefficient models, native map and original discrepancy, using the previous actual freezing, approximation and rescaled sampling construction. It retains strict dimension decrease and all-real joint native logarithm polynomiality.',
    'RoughNativeBadProgressionThinning fixes a common residue vector and native quotient on a long progression, constructs its exact jointly polynomial map, and retains actual discrepancy at every index, the original dyadic interval, roughness and smoothness of the new positive difference.',
    'RoughCofinalSubsequences upgrades finite simultaneous length/scale cofinal choice to a genuine strictly increasing scale subsequence at each prescribed length when witnesses restrict to shorter lengths. Fixed rescaling and subsequence extraction preserve power domination.',
    'RoughNativeBadFamily defines the full finite actual native bad progression data, with one joint logarithmic polynomial, positive smooth difference, rough dyadic progression and varying boxes/tests. Restriction to shorter lengths is proved. One fixed smaller quotient works at every length along strictly increasing scale subsequences, preserving scale divergence and power domination.',
    'RoughNativeSmallerBadFamily packages the actual fixed-label thinning conclusion as a finite bad progression family in the strictly smaller native group. The per-index hypotheses are actual quotient sampling discrepancies, rather than an abstract predicate.',
    'RoughNativeModelBadFamily assembles original per-index coefficient models, varying original boxes and observables, actual original discrepancies and common native polynomial into one complete finite smaller-dimensional bad progression family. Partition count and new Lipschitz bound precede the desired length; the required source length precedes varying polynomial data. Generated splitting degrees are derived, and discrepancy is not divided by piece count.',
    'RoughNativeZeroDimension proves the dimension-zero induction base: the actual native group and quotient are singletons, both nonempty uniform laws have total one, so no positive bad-index discrepancy or nonempty bad progression family is possible.'
]
REMAINING = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'Actual finite smaller-dimensional bad progression families are now assembled from original coefficient models and actual per-index discrepancies, with a common native logarithmic polynomial, uniform degree/box/test/discrepancy bounds, and rough smooth-step progression. '
    'Finite quotient selection now gives genuine lengthwise strictly increasing scale subsequences, preserving scale divergence and power domination; the zero-dimensional induction base is proved. '
    'The quantitative Leibman obstruction and its fixed finite nonzero character list must still supply the original coefficient obstructions, including corrected arbitrary-box comparison and stretched-filtration applicability. '
    'Apply the already proved actual affine obstruction interpolation and constant-term fractional thinning uniformly to entire bad families, connect the arithmetic large-scale thresholds and positive fixed discrepancy budgets to the new native model bad-family constructor, and finish dimension induction. '
    'Finite density extraction from exceptional sets and the full uniform rough-step comparison remain open. '
    'Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
REVIEW = [
    'The Prop definitions record actual native group maps, finite sampling supports and real observables. They are not axioms, external truth assumptions or assertions that bad families exist.',
    'The model bad-family theorem constructs every selected discrepancy through the previous proved single-index descent and then finite van der Waerden thinning. It does not assume the desired smaller bad family as a premise.',
    'Source progression length may depend on requested length and fixed finite labels. Partition count, finite quotient family, Lipschitz bound, discrepancy budget and degree transformation do not depend on requested length.',
    'The chosen residue vector is common only on the selected finite progression; it may vary with scale or length. It enters the polynomial coefficients, not the chosen quotient lattice. Only the finite coset index must be fixed for the dimension induction.',
    'The same group-valued map handles every retained progression index. Its native logarithm is an actual vector polynomial at all real simultaneous progression and spatial parameters. Arbitrary changing boxes and observables remain permitted.',
    'Length downward closure is proved for actual native bad-family witnesses. Joint cofinal length/scale choice without this closure would not by itself imply infinitely many scales at a fixed prescribed length; the new proof explicitly uses closure before extracting strictly increasing subsequences.',
    'Scale divergence is retained separately from power domination. Finite choice and increasing subsequences do not silently replace the original asymptotic growth hypotheses.',
    'Dimension-zero discrepancies vanish using both positive-cardinality hypotheses. Uniform masses on an empty set have zero total, and are not falsely treated as probabilities.',
    'The original nonzero character, rational direction period, coefficient models and initial bad-family data remain explicit prerequisites. The theorem does not provide the missing quantitative Leibman input or assert a completed rough-step theorem.',
    'The new native families currently use real observables. The complex-observable formulation in the paper still needs an explicit real-component reduction when the full proposition is assembled.',
    'Paper comparison covers pinned 06_rough_progressions lines 314-359 and 553-584: fixed lengthwise subsequences, finite group choice, zero-dimensional base, varying tests and boxes, and smaller-dimensional family construction.',
    'All retained proof sources and transitive axiom sets are unchanged; fresh focused checks, full build, axiom reports and pinned paper checks are author-side verification.'
]
src = Path(OLD+'-audit.py').read_text(encoding='utf-8')
src = src.replace("PREFIX = '"+OLD+"'", "PREFIX = '"+PREFIX+"'")
src = src.replace("OLD = 'round-rough-labelled-native-tests'", "OLD = '"+OLD+"'")
start = src.index('MODULES = ')
end = src.index('\ndef declarations():', start)
src = src[:start]+f'MODULES = {MODULES!r}\nCOMPONENTS = {COMPONENTS!r}\nREMAINING = {REMAINING!r}\n'+src[end:]
start = src.index('        application_review=COMPONENTS+')
end = src.index('\n        verified=summary', start)
src = src[:start]+f'        application_review=COMPONENTS+{REVIEW!r}+[REMAINING],'+src[end:]
src = src.replace("reference_scope='06_rough_progressions actual native discrepancy descent, uniform geometric thresholds and fixed-label joint polynomial reparametrization'", "reference_scope='06_rough_progressions actual smaller native bad families, lengthwise scale subsequences and zero-dimensional base'")
Path(PREFIX+'-audit.py').write_text(src, encoding='utf-8')
