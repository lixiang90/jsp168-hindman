from pathlib import Path
import json
import re

prefix = 'round-mv-binomial-inverse'
old = 'round-torus-mv-inverse'
modules = ['Hindman168/'+name+'.lean' for name in [
    'MvBinomialCoefficients', 'MvBinomialMonomialExpansion',
    'MvPolynomialBinomialExpansion', 'MvBinomialCoefficientModOne', 'MvBinomialPolynomialInverse']]
components = [
    'The fixed FULL exponent box including zero and true NATURAL INTEGER tensor Stirling weights are defined before polynomial data. Exact coordinate membership, original bounded-weight membership, true zero weights below any coordinate and true nonzero-weight total-degree monotonicity are proved.',
    'The actual univariate polynomial Stirling identity is mapped into each actual MvPolynomial coordinate. True finite product/sum exchange and ACTUAL positive factorial cancellation yield exact ordinary monomial expansion in the ORIGINAL roughMvBinomialPolynomial basis, with genuine natural integer weights. No multivariate basis identity is assumed.',
    'Every ACTUAL original polynomial of totalDegree<=D has true support in the fixed full exponent box and a TRUE binomial-basis polynomial expansion with computed coefficients. Original binomial coefficients above totalDegree D are genuinely zero. Actual projection linearity and exact constant-plus-positive-index form used in the paper are proved, retaining zero degree/dimension. No assumed representation or correspondence.',
    'One fixed positive natural tensor coefficient budget, equal to scalarBinomialCoefficientBudget(D)^inputDimension, contains EVERY actual Stirling row. True integer weighted modular norm bound, vanishing low-degree weights and N>=1 give actual N^-totalDegree preservation. The lower-weight parameter handles nonconstant-only or all-coefficient inputs without borrowing absent constant control.',
    'COMPLETE genuine scalar and standard TARGET-TORUS binomial observable inverses are proved for every fixed dimension/degree and EVERY positive original N, retaining the SAME original multiplier/nonzero horizontal character. The genuine scalar original large-box binomial small-value inverse controls ALL binomial coefficients INCLUDING constant and eps=0 with SAME q and retained original large-N threshold. All bounds precede coefficients,N,F,eps; no character, inverse or coefficient existence assumed.'
]
review = [
    'The full exponent box is actual piFinset(range(D+1)) independent of p and includes zero, including the unique empty vector at zero dimension. Every actual support exponent has total weight<=D and each coordinate<=D, so its true Finsupp equivalence belongs to the box. Finsupp.sum_of_support_subset and actual p.as_sum prove the original polynomial expansion; missing coefficients are genuinely zero.',
    'Tensor weights are product_j (I_j! * StirlingSecond(J_j,I_j)), actual NATURAL INTEGERS. StirlingSecond(J_j,I_j)=0 when J_j<I_j gives a true zero product. Nonzero weight implies every original exponent at least the output exponent and hence total original weight>=total output weight. This is an actual algebraic proof, not an assumed triangularity law.',
    'The true retained univariate X^r Stirling identity is sent through actual Polynomial.eval2RingHom(MvPolynomial.C)(X_j). Actual polynomial maps preserve powers/sums/products. True Finset.prod_univ_sum gives tensor expansion. Original roughMvBinomialPolynomial is EXACTLY product factorial inverses times product falling factors; real factorial positivity permits exact cancellation in the REAL coefficient ring. No quotient-circle division or new binomial basis naming shortcut is used.',
    'Double finite-sum exchange and true original polynomial support expansion prove actual p=sum_I C(alpha_I)*roughMvBinomialPolynomial(I). alpha_I is computed from SAME original beta_J with true integer weights. Actual above-degree zero coefficients and true zero weights remove all total-degree>D output terms. The original paper constant-plus-positive-degree expansion is proved exactly, including actual basis at zero=1, all-zero weight iff zero vector, and zero not in positive index set.',
    'The actual coefficient of the character projection is exactly sum_j k_j*alpha_I(p_j), by true original monomial projection coefficients and finite sum exchange. The same original vector polynomial and SAME original character appear in both representations. No independent alpha values, representative selection, coefficient preservation or expansion is supplied as an unproved input.',
    'Row budget is a true product of the actual one-coordinate row sums via Finset.prod_univ_sum. Every actual output coordinate I_j<=D allows the retained PROVED scalar row budget; true product inequality yields the fixed tensor budget scalarBinomialCoefficientBudget(D)^dimension. It is genuinely positive, including dimension zero. The budget precedes arbitrary coefficients,N and accuracy.',
    'For modular transfer, SAME q*alpha_I is an ACTUAL finite INTEGER weighted sum of SAME q*beta_J. The retained nearest-integer weighted modular inequality is proved. True zero weights remove all J below the permitted lower weight; nonzero weights ensure |J|>=|I|, so genuine N^|I|<=N^|J| at N>=1 retains N^-|I| errors. Positive-weight observable input never borrows constant control; all-weight small-value input legitimately controls constant. Every natural weight is nonnegative and its actual row sum is bounded by fixed budget.',
    'Scalar binomial observable result applies the GENUINELY PROVED complete scalar observable inverse to SAME p/N/F, retains SAME q, and increases only fixed budget. Scalar binomial small-value result applies the GENUINELY PROVED original all-coefficient small-value inverse with its actual N>=A condition and zero-tolerance case, retains SAME q and SAME original samples, and enlarges one fixed original length/error budget. Above-degree binomial coefficients are genuinely zero and all multiindices are covered.',
    'Standard target-torus result applies the GENUINELY PROVED torus monomial inverse to SAME vector p/N/F, producing ACTUAL nonzero v. Actual projection alpha linearity reduces original projected binomial errors to binomial coefficients of the SAME true scalar projection xi_v(p). True projection degree and integer row estimate retain SAME v and EVERY positive original coefficient. Character l1 size remains the ORIGINAL bound; uniform enlarged B contains both original size and tensor error. No character is reselected and no extra multiplier existence assumed. All positive N, fixed arbitrary target/input dimensions and degrees are covered.',
    'This proves the standard TARGET-TORUS binomial coefficient form of the corrected equal-cube input, and genuine scalar all-coefficient binomial small-value input. It does not prove the native/nonabelian quantitative Leibman orbit inverse, the SEPARATE finite-list interval Gowers-to-nilsequence correlation existence HasNativePeriodicIntervalInverse, HasAlignmentMonomialRecurrence, general rough-step comparison or full positive separated extraction. Full StrongConjecture/public repo/PR/prize application NOT complete.',
    'Primary route: fixed OpenAI Section 06_rough_progressions actual binomial coefficients and corrected equal-side statement; true Mathlib finite polynomial/product machinery and retained genuine scalar/torus inverse. Fixed-data constants only; no power-law delta rates asserted. Every old registered source/axiom set and pinned OpenAI/Lean/mathlib/PNT+ data retained. Author verification only, not independent kernel replay or external peer review.'
]
remaining = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))['last_round']['remaining']
remaining = remaining.replace(
    'Next actual multivariable binomial transformation and native/nonabelian one-parameter nilsequence inverse;',
    'Actual full multivariable monomial-to-binomial transformation, original rough-box basis expansion and genuine same-character scalar/standard-target-torus binomial inverses are now proved, including scalar constant/zero-tolerance small-value input. Next native/nonabelian orbit-equidistribution quantitative Leibman input;')
remaining = remaining.replace(
    'finish general polynomial/difference/binomial compatibility and corrected equal-cube assembly.',
    'finish native general polynomial/difference compatibility and corrected equal-cube assembly.')
src = Path(old+'-audit.py').read_text(encoding='utf-8')
src = re.sub(r'^PREFIX = .*$', lambda _: 'PREFIX = '+repr(prefix), src, count=1, flags=re.M)
src = re.sub(r'^OLD = .*$', lambda _: 'OLD = '+repr(old), src, count=1, flags=re.M)
a = src.index('MODULES = ')
b = src.index('\ndef declarations():', a)
src = src[:a]+f'MODULES = {modules!r}\nCOMPONENTS = {components!r}\nREMAINING = {remaining!r}\n'+src[b:]
a = src.index('        application_review=COMPONENTS+')
b = src.index('\n        verified=summary', a)
src = src[:a]+f'        application_review=COMPONENTS+{review!r}+[REMAINING],'+src[b:]
src = re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions: actual full multivariable binomial basis/integer coefficient transform and COMPLETE genuine same-character standard torus binomial equal-cube inverse, plus all-coefficient scalar binomial small values including zero tolerance; native/general nilsequence/full prize target still open'", src)
Path(prefix+'-audit.py').write_text(src, encoding='utf-8')
print('Prepared actual multivariable binomial inverse audit for', len(modules), 'modules.')
