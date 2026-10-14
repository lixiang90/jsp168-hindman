from pathlib import Path
import json
import re

prefix = 'round-scalar-binomial-translation'
old = 'round-polynomial-small-values'
modules = ['Hindman168/'+name+'.lean' for name in [
    'ScalarPolynomialStirlingExpansion', 'ScalarPolynomialBinomialExpansion',
    'ScalarBinomialCoefficientModOne', 'ScalarBinomialPolynomialInverse',
    'ScalarPolynomialUnitShift', 'PolynomialSmallValuesOneBased',
    'ScalarRoughBinomialCompatibility']]
components = [
    'The true polynomial identity X^n=sum_i StirlingSecond(n,i)*descPochhammer(i) is proved by actual degree induction, actual Stirling recurrence and true falling-factorial multiplication. Every weight is a natural integer.',
    'The ORIGINAL arbitrary real polynomial of degree<=D has an ACTUAL binomial-basis expansion with alpha_i=i!*sum_j beta_j*StirlingSecond(j,i). Its basis evaluates to the ACTUAL natural binomial coefficient at every natural sample. No basis expansion or coefficient correspondence is assumed.',
    'A fixed positive NATURAL coefficient budget precedes polynomial and samples. True integer weighted modular norm bounds and support j>=i transfer actual N^j errors to actual N^i binomial errors for N>=1. The lower-index parameter handles both nonconstant-only and all-coefficient hypotheses without borrowing a constant bound.',
    'The genuine arbitrary scalar Lipschitz observable inverse now supplies one bounded q for ALL ORIGINAL nonconstant BINOMIAL coefficients, on every positive N. The genuine large-box small-value inverse likewise supplies one bounded q for EVERY binomial coefficient INCLUDING constant and zero tolerance. All fixed bounds precede p,N,F,epsilon; no new inverse or character existence is assumed.',
    'The ACTUAL one-based small-value sample cardinality on Icc(1,N) equals the ACTUAL shifted zero-based cardinality via a true n->n+1 bijection. Actual integer triangular coefficient recovery for p(X+1) controls ALL ORIGINAL coefficients including the changing constant, with the SAME q and true original N^-i scales.',
    'The actual one-based large-box polynomial small-value inverse is proved on Icc(1,N), with one fixed B preceding all original real coefficients,N,epsilon. One SAME positive q<=B controls EVERY ORIGINAL coefficient, including i=0 and epsilon=0. Actual translated polynomial degree and evaluation are proved, and the original sufficiently-large-N condition is retained.',
    'The actual one-variable binomial basis and expansion agree with the retained roughMvBinomialPolynomial under the actual Mathlib unique-variable algebra equivalence. The true falling-factorial product and true algebra-map identities establish this exact rough-box compatibility; no multivariable inverse is claimed.'
]
review = [
    'Stirling induction uses descPochhammer_succ_right and the exact recurrence at every positive index. The zero index is genuinely zero at successor degree. The shifted finite sum has a genuinely zero terminal coefficient StirlingSecond(n,n+1), not an omitted boundary term. The degree-zero identity is checked directly.',
    'The actual p coefficient sum over range(D+1) is the true original polynomial by its genuine degree hypothesis. Extension of the Stirling sum uses exact zero weights above the original power degree. Exact double finite-sum exchange yields the actual binomial expansion; factorial inverse cancellation is on REAL polynomials with a proved positive factorial, never division on the quotient circle.',
    'Every transformed coefficient is an actual finite INTEGER weighted sum of the SAME q*beta_j. The modular triangle bound is the retained proved nearest-integer lemma. StirlingSecond(j,i)=0 for j<i, so no absent lower-index bound is used. For j>=i and N>=1, genuine monotonicity N^i<=N^j retains the original coefficient scale. One fixed natural budget contains every row before arbitrary coefficients and N.',
    'Both binomial inverse outputs apply the retained proved monomial inverse to the SAME actual p and SAME original samples. Output q is unchanged, while one fixed B contains multiplier and true transformed-coefficient error budgets. The observable conclusion controls positive i only; the small-value conclusion controls i=0 as well and retains its actual N>=B condition and zero-error case.',
    'The one-based set is EXACTLY Icc(1,N), not an unspecified translated distribution. A genuine Finset.card_bij proves inclusion, injectivity and surjectivity, including N=0. The actual substituted polynomial is p.comp(C(1)*X+C(1)) and evaluates at p(n+1) with true degree<=D.',
    'All original coefficient recovery, including i=0, follows from the proved scalar_polynomial_integer_coefficient_recovery at a=1,q=1. True integer weights vanish below i and have absolute value<=2^D. The translated inverse supplies ALL j including j=0; genuine N^i<=N^j gives the original N^-i estimate. The same output q is retained, and the final original-length threshold contains the original zero-based threshold. Constant translation invariance is never asserted.',
    'The rough-box compatibility theorem uses the actual uniqueAlgEquiv on the actual roughMvBinomialPolynomial, not only agreement at a finite sample. The polynomial falling-factorial product is proved by induction. The actual algebra equivalence is injective, so the true scalar expansion yields the true original rough-basis expansion under its inverse. Only the one-variable scope is claimed.',
    'Primary route remains OpenAI Section 06_rough_progressions, the corrected quantitative Leibman binomial statement and its monomial consequence. One-based auxiliary conventions of the cited Green-Tao input now have a true translation bridge. Multivariable and general nilsequence inverse, rough descent and Alignment/full extraction remain open. Fixed-data bounds only; no polynomial dependence on delta asserted. Author verification only, not independent kernel replay or peer review.'
]
remaining = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))['last_round']['remaining']
remaining = remaining.replace(
    'Multivariable scalar/higher-dimensional torus and general one-parameter nilsequence inverse and binomial compatibility remain open.',
    'Scalar monomial-to-binomial compatibility, actual rough singleton-basis expansion, and genuine one-based translation of ALL coefficients are now proved. Multivariable scalar/higher-dimensional torus and general one-parameter nilsequence inverse remain open.')
remaining = remaining.replace(
    'Next connect actual monomial/binomial compatibility and integer translation scope, then prove multivariable scalar/higher-dimensional torus and general one-parameter nilsequence inverse; finish polynomial/difference/binomial compatibility and corrected equal-cube assembly.',
    'Next prove multivariable scalar/higher-dimensional torus and general one-parameter nilsequence inverse; finish general polynomial/difference/binomial compatibility and corrected equal-cube assembly.')
src = Path(old+'-audit.py').read_text(encoding='utf-8')
src = re.sub(r'^PREFIX = .*$', lambda _: 'PREFIX = '+repr(prefix), src, count=1, flags=re.M)
src = re.sub(r'^OLD = .*$', lambda _: 'OLD = '+repr(old), src, count=1, flags=re.M)
a = src.index('MODULES = ')
b = src.index('\ndef declarations():', a)
src = src[:a]+f'MODULES = {modules!r}\nCOMPONENTS = {components!r}\nREMAINING = {remaining!r}\n'+src[b:]
a = src.index('        application_review=COMPONENTS+')
b = src.index('\n        verified=summary', a)
src = src[:a]+f'        application_review=COMPONENTS+{review!r}+[REMAINING],'+src[b:]
src = re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions: genuine scalar binomial coefficient/basis compatibility and actual one-based small-value translation including constant and zero tolerance; multivariable/general nilsequence inverse remain open'", src)
Path(prefix+'-audit.py').write_text(src, encoding='utf-8')
print('Prepared binomial/translation audit for', len(modules), 'modules.')
