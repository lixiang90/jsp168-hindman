from pathlib import Path
import re

prefix = 'round-leibman-common-character'
old = 'round-leibman-dense-directions'
modules = ['Hindman168/'+name+'.lean' for name in [
    'FiniteRealDenseWeights', 'FiniteCandidateDenseRows', 'LeibmanCubeCommonCharacter',
    'NativeFilteredHorizontalDenseSelection', 'LeibmanCubeCommonSpanningDirections']]
components = [
    'Actual finite real weights bounded by B with total sum >=delta*|T|*B have at least delta/2*|T| actual entries of weight >=delta*B/2. No ordering of complex values or common phase is assumed.',
    'Actual witnesses admitting any member of a finite candidate family have cardinality at most the sum of the actual candidate witness cardinalities. If every actual direction has delta*|S| witnesses, one common actual candidate has at least delta/(2*|A|) of the original directions, each with at least delta/(2*|A|) of the original origins. Candidate family nonemptiness is derived from actual output density, not assumed.',
    'The actual corrected equal-cube short-line theorem supplies delta/4 of the original origins for every actual direction in [0,L)^n. Conditional only on explicit analytic production of an actual candidate on every large short line, one common actual candidate has the exact delta/(8*|A|) direction and origin fractions. Original integer origins and actual floor(N/L^2) short lines are retained.',
    'Actual nonzero original Gamma-integral horizontal outputs of SAME filtered coefficient norm <=M are placed in the actual original filtered integer character grid and then filtered again by that exact norm bound. A common actual functional retains nonzeroness, original Gamma integrality and exact original norm <=M. Analytic production of these functionals remains an explicit unproved input.',
    'With actual direction-size inequality 8*d*|A|<delta*L, the same selected candidate has an actual direction subset with d*L^n<|T|*L. The previous genuine dense-direction spanning theorem applies to the actual rational monomial vectors. One common candidate therefore has a truly spanning sampled monomial family and many actual origins for every selected direction.'
]
remaining = (
    'StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'All prior original filtered lattice, horizontal classification, exact coefficient norm/grid, rational normalization, short-line averaging, dense monomial spanning, fixed-data bounded integer reconstruction and simultaneous modular multiplier results remain retained. '
    'Common candidate/character selection, actual direction and origin density extraction and its connection to genuine monomial spanning are now proved from explicit per-line analytic outputs. These outputs are not newly assumed axioms and have not been constructed. '
    'The genuine one-parameter quantitative Leibman nonzero character existence and uniform modular binomial smoothness bounds remain open. The equal-cube correction still requires actual multivariate small-value inverse coefficient estimates and actual polynomial/difference/binomial compatibility and assembly. Candidate grids and conditional common selection or reconstruction do not discharge character existence or the inverse estimates. Uniform reconstruction bounds are fixed-data existence bounds; no power-law dependence in L/delta is asserted. '
    'Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. '
    'Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. '
    'Author verification only: no independent kernel replay, external peer review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target.')
review = [
    'The dense-weight estimate bounds each original summand by delta*B/2 plus B times its actual large-value indicator; actual filter cardinality and genuine finite sums give the conclusion. It remains valid for empty direction sets and does not add an unnecessary weight lower-bound assumption.',
    'Actual candidate witness sets are a genuine finite union, so possible overlaps only increase the upper sum bound. The total sum over actual directions and candidates is commuted. Actual candidate positivity is derived from one nonempty original direction and positive original origin density. The true weighted pigeonhole principle then chooses one candidate before the same actual dense-row estimate is applied; no different candidate is selected per retained direction.',
    'The original complex cube mean only feeds the already proved short-line modulus estimate. Candidate production for the true short-line length floor(N/L^2) is an explicit hypothesis. Actual large-origin filter inclusion transports the delta/4 bound. Both final fractions are exactly delta/(8*|A|), and actual candidate membership implies a nonzero denominator.',
    'Native candidate selection uses the exact original filtered grid and actual coefficient norm, not an older independent basis or merely coordinatewise size. Every analytic output has true RoughNativeHorizontalFunctional and original norm <=M. Selection returns an actual grid member, hence the original nonzero Gamma-integral horizontal property and exact size bound; existence of the analytic outputs is not claimed.',
    'The selected direction subset is the true density filter in the original direction cube. Its exact cardinality is at least delta/(8*|A|)*L^n. With 8*d*|A|<delta*L and actual |A|>0, the original natural cardinality condition follows. Genuine Schwartz-Zippel spanning applies to the same sampled monomial vectors while preserving the same candidate and origin filters. Zero variables and empty monomial index sets are permitted; L and N are genuinely positive.',
    'This supplies the common-character finite selection and direction part of the corrected equal-cube route, conditional on the genuine one-parameter analytic outputs. Multivariate small-value inverse and analytic existence remain unproved. All six pinned OpenAI sections and prior registered proof hashes/axiom sets remain unchanged.'
]
src = Path(old+'-audit.py').read_text(encoding='utf-8')
src = re.sub(r'^PREFIX = .*$', lambda _: 'PREFIX = '+repr(prefix), src, count=1, flags=re.M)
src = re.sub(r'^OLD = .*$', lambda _: 'OLD = '+repr(old), src, count=1, flags=re.M)
a = src.index('MODULES = '); b = src.index('\ndef declarations():', a)
src = src[:a]+f'MODULES = {modules!r}\nCOMPONENTS = {components!r}\nREMAINING = {remaining!r}\n'+src[b:]
a = src.index('        application_review=COMPONENTS+'); b = src.index('\n        verified=summary', a)
src = src[:a]+f'        application_review=COMPONENTS+{review!r}+[REMAINING],'+src[b:]
src = re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions corrected equal-cube route: one common candidate, actual direction/origin density and genuine sampled monomial spanning; genuine analytic outputs remain an explicit unproved input'", src)
Path(prefix+'-audit.py').write_text(src, encoding='utf-8')
print('Prepared actual common-character selection audit for', len(modules), 'modules.')
