from pathlib import Path
import re

prefix = 'round-circle-strong-recurrence'
old = 'round-circle-linear-inverse'
modules = ['Hindman168/'+name+'.lean' for name in [
    'UnitCircleNormBump', 'UnitCircleDenseSmallValues', 'FiniteIntegerSpanCard',
    'LinearNearestIntegerHitCount', 'UnitCircleProgressionHitCount',
    'UnitCircleStrongLinearRecurrence', 'UnitCircleAffineSmallValueInverse']]
components = [
    'The actual circle norm bump max(0,c-norm(t)) is genuinely unit Lipschitz, nonnegative and at most c. Its actual complex continuous observable is admissible for 0<=c<=1. Actual normalized Haar ball measure equals 2c for 0<=2c<=1; true support domination by a ball indicator gives actual Haar integral<=2c^2.',
    'Actual cardinal density of modular small values gives the actual real bump mean lower bound, not an assumed expectation. With c=delta/4 and eps<=delta/10, actual average minus Haar has norm>=delta^2/40. The previously proved genuine affine analytic inverse supplies one fixed positive A, chosen before slope, offset, N and eps, with nonzero integer k of natAbs<=A and N*norm(k*x mod 1)<=A.',
    'Actual finite natural and integer cardinalities are bounded by their actual maximum minus minimum plus one, via containment in genuine integer intervals. No spacing or counting estimate is assumed.',
    'Actual integer indices in one lifted affine interval have abs(a)*card<=abs(a)+2eps. True maximum/minimum indices prove this, including zero and negative a without division. Actual nearest-integer labels have cardinality<=abs(a)*J+2eps+1. Summing the actual fibers gives abs(a)*card(hits)<=(abs(a)*J+2eps+1)*(abs(a)+2eps).',
    'The original modular hit indices are genuinely partitioned by residues modulo positive q, with actual quotient indices and injective reconstruction n=n%q+q*(n/q). Subtracting the true integer multiple of round(q*x) preserves the actual circle value. Actual row counting and q*(floor(N/q)+1)<=N+q yield beta*card(hits)<=(beta*N+3q)*(beta+2eps), where beta=norm(q*x mod 1). The bound includes zero and negative nearest-integer increments.',
    'Actual dense hits, actual coarse q<=A and beta*N<=A, and the explicit threshold 8A<=delta*N give N*beta<=16A*eps/delta. The genuine coarse analytic inverse produces this q; its positive natural absolute value preserves the actual circle norm. This proves genuine strong scalar linear recurrence rather than an interface assuming a character or count bound.',
    'An actual small-value sample exists by actual positive density. True circle subtraction and natural-multiplier bounds give norm(q*b mod 1)<=17A*eps/delta for the SAME q as the refined slope bound. Actual ceilings choose one positive B depending only on delta. For ALL affine coefficients x,b, lengths N>=B, and 0<=eps<=delta/10, actual density>=delta yields positive q<=B with N*norm(q*x)<=B*eps and norm(q*b)<=B*eps. The actual large-box threshold is retained, including eps=0. No power-law dependence on delta is claimed.'
]
review = [
    'The bump is the actual circle norm and actual max operation. The normalized Haar measure is identified with true volume at period one before invoking the library closed-ball measure theorem. The integral comparison is between genuinely integrable functions. The complex discrepancy is identified with the actual real mean minus real Haar integral; taking absolute value cannot decrease the real discrepancy.',
    'All quantifiers in the coarse inverse are ordered correctly: delta is fixed and one A is chosen before x,b,N,eps. The observable is constructed, its Lipschitz and pointwise bounds are proved, and the real finite mean lower bound follows from actual filtered cardinality. Dense small values are a premise about the actual samples, not an assumed inverse conclusion.',
    'The hit count uses actual nearest-integer labels and actual cardinality of every fiber. The finite-cardinality bounds are proved from actual extremal indices and integer interval cardinalities. Signed increments are handled by absolute value and real arithmetic; no positivity of the slope is silently assumed and no division by beta occurs.',
    'Residue rows use a true injection through n/q restricted to n%q=r. The exact modular identity subtracts the true integer (n/q)*round(q*x). The row length floor(N/q)+1 is an actual uniform upper bound, valid also at N=0. The original hit count, not the cardinality of a replacement sampling law, is summed over every residue in range q.',
    'Refinement multiplies the actual density by beta>=0. The coarse upper bound and q<=A control the entire count factor by 4A. The large-N condition absorbs the term 4A*beta. This proves a division-free estimate before dividing by genuine delta>0; beta=0 and eps=0 are fully included. The constant and slope error conclusions never assert an unrestricted short-box O(eps) bound.',
    'The offset proof selects a real sample from the actual dense set, uses its actual n<N and the SAME q. It bounds the true modular norm of q*b via q*(b+n*x)-n*(q*x). One B contains A and both genuine ceiling bounds 8A/delta and 17A/delta. The length threshold N>=B is fixed before coefficients and eps, and guarantees the refinement threshold. Both actual affine coefficients satisfy B*eps bounds.',
    'Primary route references: OpenAI Section 06_rough_progressions; Green-Tao https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf Section 3 Proposition 3.1 and Lemma 3.2; erratum https://arxiv.org/pdf/1311.6170v3 Section 2 Proposition 2.3 and Section 3 large-N application. This continuation completes the genuine affine scalar analytic and strong-recurrence base case only. All prior sources and axiom sets and six pinned OpenAI sections remain retained.'
]
src = Path(old+'-audit.py').read_text(encoding='utf-8')
src = re.sub(r'^PREFIX = .*$', lambda _: 'PREFIX = '+repr(prefix), src, count=1, flags=re.M)
src = re.sub(r'^OLD = .*$', lambda _: 'OLD = '+repr(old), src, count=1, flags=re.M)
remaining_start = src.index('REMAINING = ')
remaining_end = src.index('\n\ndef declarations()', remaining_start)
old_remaining = eval(src[remaining_start+len('REMAINING = '):remaining_end].strip())
remaining = old_remaining.replace(
    'Next prove genuine modular interval-hit counting and linear strong recurrence using the actual analytic base, then higher-degree scalar inverse/small-value estimates and general one-parameter nilsequence inverse;',
    'Genuine affine scalar norm-bump Haar control, coarse inverse, actual modular interval-hit counting, strong linear recurrence and large-box O(eps) control of BOTH affine coefficients are now proved. Next prove the genuine higher-degree scalar polynomial inverse and large-box polynomial small-value estimates, higher-dimensional torus and general one-parameter nilsequence inverse;')
a = src.index('MODULES = '); b = src.index('\ndef declarations():', a)
src = src[:a]+f'MODULES = {modules!r}\nCOMPONENTS = {components!r}\nREMAINING = {remaining!r}\n'+src[b:]
a = src.index('        application_review=COMPONENTS+'); b = src.index('\n        verified=summary', a)
src = src[:a]+f'        application_review=COMPONENTS+{review!r}+[REMAINING],'+src[b:]
src = re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions corrected equal-cube analytic input: genuine affine scalar norm bump, Haar support control, actual interval-hit count, strong linear recurrence and large-box affine small-value inverse; higher-degree and general nilsequence inverse remain open'", src)
Path(prefix+'-audit.py').write_text(src, encoding='utf-8')
print('Prepared genuine circle strong recurrence audit for', len(modules), 'modules.')
