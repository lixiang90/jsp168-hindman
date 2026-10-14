from pathlib import Path

PREFIX = 'round-rough-native-obstruction-descent'
OLD = 'round-rough-native-bad-family'
MODULES = ['RoughNativeDescentBudgets', 'RoughNativeAsymptoticModelBadFamily',
    'RoughJointScalarReparametrization', 'RoughNativeJointCoefficientThinning',
    'RoughNativeIntegerizedBadFamily', 'RoughNativeObstructionBadFamily']
MODULES = ['Hindman168/'+m+'.lean' for m in MODULES]
COMPONENTS = [
    'RoughNativeDescentBudgets derives a common eventual scale threshold for every rough dyadic step and original box. It gives positivity, coprimality with the fixed rational period, both required integer partition side bounds, rescaled size and a strictly positive fixed discrepancy budget from power domination.',
    'RoughNativeAsymptoticModelBadFamily assembles a strictly smaller actual bad progression family from the original coefficient models and discrepancies using the derived thresholds. Partition count and Lipschitz bound precede the requested length; no arithmetic coprimality, partition size or error-gap premise is left to the caller.',
    'RoughJointScalarReparametrization proves the actual scalar joint polynomial evaluation identity under affine progression substitution, preservation of weighted spatial degrees and the degree bound needed for interpolation of step powers times coefficient polynomials.',
    'RoughNativeJointCoefficientThinning constructs an integer-valued rational constant polynomial on a retained progression using proved fractional-part thinning. It preserves the same actual native map, all-real native logarithmic polynomial, specified subgroup, positive-degree coefficient models and fixed joint degree.',
    'RoughNativeIntegerizedBadFamily applies constant-term thinning to entire source families before the geometric descent. It restricts varying original boxes and tests to the same retained progression, preserves the smooth difference and rough dyadic steps, and obtains a smaller actual family with fixed discrepancy eta/2.',
    'RoughNativeObstructionBadFamily starts with actual affine-substituted scalar coefficients modulo one and the paper scale-divergence and all-positive-real-power ratio hypotheses. It extracts the rational positive-degree models uniformly, supplies constant-term integrality and all scale budgets, and constructs the actual strictly smaller native bad family. Source length is chosen before varying polynomial data, original boxes, tests and obstruction translations.'
]
REMAINING = ('StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'Actual affine coefficient obstructions now yield finite smaller-dimensional native bad families with a common all-real logarithmic polynomial, fixed degree and discrepancy bounds; constant-term thinning, rational coefficient models and arithmetic/geometric thresholds are derived rather than assumed. '
    'The quantitative Leibman obstruction and its fixed finite nonzero character list must still provide these actual coefficient obstructions, including corrected arbitrary-box comparison and stretched-filtration applicability. '
    'Extract the scalar joint polynomial from the native logarithmic polynomial and a selected character, connect finite character selection to this constructor, and finish the dimension induction using the proved lengthwise cofinal subsequence and zero-dimensional base. '
    'The real-observable interfaces still need an explicit complex-component discrepancy reduction. Finite density extraction from exceptional sets and the full uniform rough-step comparison remain open. '
    'Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.')
REVIEW = [
    'The final obstruction theorem does not assume positive-degree rational coefficient models, an integer-valued constant-term model, period coprimality, minimum partition side lengths or a discrepancy error gap. Each is constructed from the stated actual coefficient obstructions and asymptotic hypotheses.',
    'The horizontal character, rational subgroup, rational direction, its lattice period, scalar polynomial representation and original bad discrepancies remain explicit hypotheses. Quantitative Leibman and existence of its finite character list are not smuggled into the proof as axioms or conclusions.',
    'Partition count and output Lipschitz bound are independent of target progression length. The interpolation source length is at least 2*q+2 and at least the later thinning source length; it is selected before all varying polynomial, box and test data. The eventual scale threshold may depend on this selected source length.',
    'The coefficient interpolation error constant depends on degree, spatial support and the fixed obstruction bound, but not on source length. Positive spatial degree is checked for every retained coefficient, so the constant coefficient is handled separately by fractional-part thinning.',
    'Affine progression substitution preserves the actual native map and logarithm at all real coordinates, rather than only sampled integer indices. The degree bound includes the progression variable and weighted spatial degree.',
    'The original per-index tests and boxes may vary; they are pulled back along the same selected progression as the map and scalar models. Integer casts in the sampling-step identity are checked explicitly.',
    'Coprimality with the fixed positive period is derived from primorial roughness once w exceeds that period. Positivity of all dyadic steps follows from eventual scale at least one. Both original integer side inequalities follow from the same real lower box-size bound.',
    'Freezing and approximation errors are each eta/32; the geometric boundary term is eventually small enough that eta/2 remains a strict surviving discrepancy. The selection does not divide discrepancy by the number of pieces.',
    'The output is a finite family at each requested length and eventual scale. The already proved fixed-quotient cofinal subsequence theorem is still needed when assembling an infinite bad-family contradiction; no such assembly is claimed here.',
    'Local source inventory review found no proved corrected quantitative Leibman theorem: the OAI LeibmanSquare and MalcevCharacters modules are supporting algebraic constructions, not that analytic theorem. This absence is remaining proof work, not evidence of an unavoidable obstruction.',
    'Paper comparison covers pinned 06_rough_progressions coefficient interpolation, constant fractional-part thinning, the kernel coset descent and its final smaller-family construction. All six pinned sections are checked against their fixed Git content.',
    'All retained proof sources and transitive axiom sets are unchanged. Focused checks, full build and selected axiom reports are author-side verification; the full target and independent replay are not claimed.'
]
src = Path(OLD+'-audit.py').read_text(encoding='utf-8')
src = src.replace("PREFIX = '"+OLD+"'", "PREFIX = '"+PREFIX+"'")
src = src.replace("OLD = 'round-rough-native-piece-descent'", "OLD = '"+OLD+"'")
start = src.index('MODULES = ')
end = src.index('\ndef declarations():', start)
src = src[:start]+f'MODULES = {MODULES!r}\nCOMPONENTS = {COMPONENTS!r}\nREMAINING = {REMAINING!r}\n'+src[end:]
start = src.index('        application_review=COMPONENTS+')
end = src.index('\n        verified=summary', start)
src = src[:start]+f'        application_review=COMPONENTS+{REVIEW!r}+[REMAINING],'+src[end:]
src = src.replace("reference_scope='06_rough_progressions actual smaller native bad families, lengthwise scale subsequences and zero-dimensional base'", "reference_scope='06_rough_progressions actual affine coefficient obstructions through integerized native smaller-family descent'")
Path(PREFIX+'-audit.py').write_text(src, encoding='utf-8')
