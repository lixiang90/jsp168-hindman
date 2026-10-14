from pathlib import Path
import json
import re

prefix = 'round-native-rational-dense-nonlinear-separation'
old = 'round-native-rational-scalar-difference-formula'
base = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained = {f['path'] for f in base['files']}
modules = sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules) == 7, modules
components = [
    'The EXACT second coefficient of P+Q(X+h)-Q+sigma*X is the evaluation of a CONSTRUCTED shift polynomial: HasseDeriv(2,Q)+C(P_2-Q_2). The arbitrary sigma term is proved absent; every positive shift-polynomial coefficient is choose(j+2,2)*Q_(j+2). Its true degree is bounded by the original D.',
    'Genuine dense small-value inverse is APPLIED to this ACTUAL constructed polynomial in h. Fixed natural B/T precede ALL raw P/Q coefficients, arbitrary sigma functions, original N and dense subsets U. The true error epsilon=A/N^2 is retained, and a genuine large-N threshold ensures epsilon<=delta/10. Actual useful shifts remain in SAME original range N.',
    'Original N^j bounds on EVERY higher Q monomial coefficient with its integer choose(j,2) factor are PROVED for 3<=j<=D. A genuine finite-product multiplier construction removes ALL such factors with ONE positive bounded natural multiplier, independent of source coefficients in its BOUND. No separate small-summand claim or arbitrary scalar-divisibility assumption is used.',
    'BOTH original higher monomial and paper-binomial Q coefficients are bounded with the SAME actual multiplier and SAME original N^-degree scale. Integer triangular Stirling weights transfer the bounds without importing an unavailable constant/linear/quadratic bound. The range 3<=j<=D is explicit; linear residual and quadratic recovery remain OPEN.',
    'Unit-variable scalar polynomials convert EXACTLY to ordinary real univariate polynomials, with ALL raw coefficients, every real evaluation, degree bound and translations preserved. Actual compact original diagonal P/nonlinear Q/commutator slope sigma are explicitly named from the SAME native data and character. The COMPLETE compact relative scalar formula is transported literally, and its ACTUAL second coefficient bound is derived from the SAME original relative coefficient table.',
    'Genuine native common-relative-character extraction is COMBINED with this complete higher coefficient separation. ALL native character-grid/norm/density/multiplier/coefficient budgets and large-N thresholds precede ALL original unbounded polynomials, observations and sample lengths. The sole inverse premise is the FULL actual lower-degree child inverse. Actual dense shift set, original combined coefficient bounds and ACTUAL Q higher monomial/binomial bounds are preserved together; original horizontal reconstruction/full inverse remain OPEN.'
]
remaining = base['last_round']['remaining']
remaining += '\nLATEST DENSE NONLINEAR MILESTONE: Actual second-coefficient shift polynomial and genuine dense small-value inverse yield ONE bounded common natural multiplier for BOTH ACTUAL Q higher monomial/paper-binomial coefficients at ORIGINAL N^-j scale (3<=j<=ell). This is APPLIED to the SAME native compact Q/actual common relative character and preserves actual dense useful U and BOTH combined relative coefficient bounds. NEXT: true linear-coefficient remainder estimate after removing higher Q, actual quadratic/binomial alpha identification, P(1)+alpha*h+sigma(h) modulo-one relation on SAME dense shifts (finish Green-Tao Lemma 7.6), bracket-polynomial alternative and genuine original character reconstruction or smaller rational nonlinearity filtration/factorization. Large-N threshold is explicit; small-N original inverse branch is not newly claimed. Full original inverse, corrected multiparameter inverse, interval Gowers correlation inverse, rough progressions, Alignment and StrongConjecture remain UNPROVED. No unavoidable obstruction found; no public repository/PR/prize application yet.'
text = Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
    text = re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),text,flags=re.M)
text = text.replace('Audit genuine original F_2 conjugation/commutator character identities, constructed nonlinear coefficient polynomial and COMPLETE actual scalar difference formula on the SAME compact relative polynomial.',
    'Audit actual dense second-coefficient separation, one bounded common higher multiplier for BOTH nonlinear tables, exact Unit/univariate transport and SAME native compact common-character application.')
text = re.sub(r"reference_scope='[^']*'", "reference_scope='OpenAI 06_rough_progressions quantitative Leibman route; Green-Tao section 7 Lemma 7.6 higher-coefficient step: actual second-coefficient dense separation and SAME native Q application; linear residual/bracket reconstruction/full target open'",text)
Path(prefix+'-audit.py').write_text(text,encoding='utf-8')
review = '''JSP-000168 / Erdos #172: actual dense higher nonlinear coefficient separation
Author mathematical review, 2026-10-13. Verdict: Partial coverage.
NOT independent kernel replay or external peer review.

Original target: all finite colorings of the positive integers have arbitrarily
large positive distinct monochromatic finite-sums/finite-products witnesses.
StrongConjecture is UNPROVED. This round continues the quantitative Leibman
input on the pinned OpenAI route; it does not assert the full inverse.
Original pinned six-section source:
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026,
06_rough_progressions. Auxiliary route:
https://arxiv.org/html/0709.3562v4 , section 7, Lemma 7.6 higher coefficient stage;
corrected multiparameter scope: https://arxiv.org/html/1311.6170v3 .

1. The ACTUAL shift polynomial
For real univariate P/Q and arbitrary real sigma, consider
R_h(X)=P(X)+Q(X+h)-Q(X)+sigma(h)*X. Its actual coefficient of X^2 equals
F(h), where F=HasseDeriv(2,Q)+C(P_2-Q_2). The equality is proved by the actual
Taylor coefficient theorem. Sigma has zero second coefficient. For j>0,
F_j=choose(j+2,2)*Q_(j+2). The bound degree(F)<=D follows from true Q degree;
the proof does not assume any cap on raw Q coefficients or smoothness of sigma.

2. Apply the existing COMPLETE small-value inverse
Dense useful shifts U are literally a subset of range N. Their combined
second-coefficient bound is N^2*norm(F(h) mod 1)<=A. Hence the SAME integer
shifts are actual small values of F with epsilon=A/N^2. The already proved
polynomial_small_values_inverse covers all coefficients, including constant,
and epsilon=0, and has NO remaining degree-induction premise.

Choose its B before ALL P/Q, sigma, N and U. The genuine threshold
T=B+ceil(10*A/delta)+1 forces N>=B and epsilon<=delta/10, using N>=1 and
N^2>=N. This is an explicit actual large-N condition; it is not dropped or
silently treated as the full inverse on all original lengths. U cardinality
transfers to the actual F small-value filter by inclusion. No replacement
sample, shorter scale, or hypothetical dense set is substituted.

The actual inverse gives ONE q<=B controlling all F coefficients at N^-j
scale times epsilon. For original j>=3, multiplying by N^2 and the exact
F_(j-2) identity yields N^j*norm(q*choose(j,2)*Q_j)<=B*A. The algebra preserves
the exact original j exponent and handles nonnegative A, including zero.

3. ONE common multiplier
The factors d_j=q*choose(j,2) for j in Icc(3,D) are positive. Each is bounded
by K=B*(1+sum_{j in Icc(3,D)} choose(j,2))+1, fixed before coefficients.
The previously checked finite_mod_one_common_multiplier uses the ACTUAL
product of these d_j and proves a fixed bound S=K^(card(Icc(3,D))+1).
It applies separately to x=Q_j and epsilon=A/N^j, so the SAME common M controls
ALL higher Q_j with original N^-j scale. An empty higher-index set yields an
actual positive product and a vacuous higher conclusion, never an invented
degree-two inverse proof. Natural multiplication on the circle is used with
its proved norm inequality, not with unsupported division of a circle norm.

4. BOTH actual coefficient tables
The scalar binomial table is an INTEGER triangular combination of original
monomial coefficients. Its row budget and true scale comparison for N>=1
transfer the higher monomial bounds to binomial bounds. The helper's lower
index is explicitly 3. Thus no unavailable constant/linear/quadratic bound
is imported. One common M suffices for BOTH higher tables; only the fixed
real error budget grows. This is the higher-coefficient portion of the
separation argument, not completion of its linear/quadratic residual.

5. EXACT Unit/univariate/native correspondence
The Unit-variable polynomial is mapped by the actual mathlib unique-variable
algebra equivalence. Its coefficient j is EXACTLY the Mv coefficient at the
single Unit index j, all evaluations agree, and true total-degree bounds give
ordinary natDegree bounds. Substituting X+h is preserved by evaluation and
polynomial uniqueness. This is an actual bridge, not a renaming of definitions.

Actual compact diagonal P, actual compact nonlinear Q, and actual commutator
slope sigma(h) are constructed from SAME original p, weighted hp, compact
normalization/zero proofs, selected relative chi and original compact shift
representative. The prior COMPLETE native scalar equality maps exactly to
R_h(X). The relative source table at Unit index 2 gives the actual second
coefficient bound when ell>=2; its finite degree and actual N are unchanged.
Original p coefficients remain unbounded. No alternate P/Q or new native
compatibility premise is supplied.

6. Actual native application and quantifier order
The prior native common-relative-character theorem supplies fixed A/R/rho/C
before p/hp/F/N. Take mu=min(rho,1), which is positive and <=1; useful U retains
mu-density without assuming rho<=1. Apply the FULL generic separation theorem
at ell, mu and R, fixing S/T/higher budget before p/hp/F/N. After choosing the
actual common relative chi and actual useful U, all generic inputs are PROVED:
true Q degree, exact second coefficient, exact range N and actual cardinality.
Both higher Q tables are returned with an actual M<=S. Enlarging one fixed
budget preserves BOTH original combined relative tables on SAME U as well.

The native theorem's sole inverse premise is the FULL desired inverse on the
ACTUAL relative-then-terminal lower-degree child. This is not circularly
claimed as already proved for all degrees. Original mean and its true
large-N/large-signal requirements are retained. Relative chi is genuinely
nonzero/horizontal/norm-bounded and in the same fixed finite list. No original
nonzero horizontal character is claimed from relative nonzeroness alone.

7. Remaining exact tasks
Finish the true linear coefficient remainder bound after removing the bounded
higher Q coefficients; identify the quadratic paper-binomial alpha with its
ordinary coefficient, with the actual integral correction and N scales;
derive P(1)+alpha*h+sigma(h) mod-one on SAME useful shifts. This completes the
remaining scalar part of the auxiliary lemma. Next are the genuine bracket
alternative, original character construction/finite grid/operator/BOTH raw
coefficient bounds, or actual smaller rational filtration/factorization in
the reducible case. The secondary nonlinearity induction remains necessary.
Small combined coefficients alone do not control small individual summands.

The full original inverse, corrected multivariate inverse, separate interval
Gowers correlation inverse, rough progressions, cube/Alignment/positivity and
final original separated FS/FP extraction remain UNPROVED. No unavoidable
obstruction has been found. Publication/application milestone not reached.

Author checks: actual focused autoImplicit=false checks of every new module,
full root build and all registered axiom reports; unchanged old proof hashes
and axiom sets; Lean 4.32.2/pinned mathlib/PNT+ and six OpenAI section hashes.
Final raw logs are authoritative. Only standard classical Lean foundations
are allowed. No sorry/admit/custom axiom/native computation/kernel bypass.
This is not independent kernel replay, external review or prize approval.

Explicit judgments: intermediate work addresses original scope CONDITIONALLY;
exact saved source passes author checks only as confirmed by final logs; does
NOT fully solve original problem; does NOT meet full Lean completeness for
an award submission. Goal ACTIVE; no public repository/PR/prize application.
'''
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
print(json.dumps(modules))
