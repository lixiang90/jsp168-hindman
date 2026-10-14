from pathlib import Path
import json
import re

prefix='round-native-rational-small-rational-factors'
old='round-native-rational-nonlinearity-factorization'
base=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained={f['path'] for f in base['files']}
modules=sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules)==13,modules
components=[
    'SAME original dense N-scaled affine circle samples yield true N^2 slope and N offset bounds with positive bounded natural multiplier and thresholds BEFORE all raw sources. ACTUAL zero original commutator pairing makes every native bracket coefficient zero, giving exactly M*P(1)+M*Q_bin2*h. No assumed second coefficient is supplied.',
    'ACTUAL quadratic remainder and original high nonlinear monomial bounds complete the missing Q second coefficient. A genuine common positive natural multiplier M_new=2*r*M_old retains BOTH complete Q monomial/binomial tables from degree TWO, BOTH higher P tables and actual P(1) bound. All multiplier and coefficient budgets precede raw p/N. The true affine completion lemma recovers SAME original dense bracket samples at the new common multiplier.',
    'The canonical rational difference extension F applied to ACTUAL raw source p has higher monomial coefficients EXACTLY equal to native compact Q, using real F_2 restriction, actual linear-step and both native normalization horizontal identities. Nonlinear part Q_F removes true constant/linear coefficients. EVERY coefficient from two upward, including higher binomial coefficients, agrees exactly; the entire polynomials Q and Q_F are NOT identified.',
    'TRUE nearest integers z_i=round(M*coeff_i Q_F) define an ACTUAL integer numerator and rational R=sum(z_i/M)*X^i with ONE positive denominator M. E=Q_F-R has actual degree<=highest j, true coefficients zero at zero/one and REAL original-scale bounds M*N^i*abs(coeff_i E)<=B. Unbounded integer numerators are retained. No circle estimate is silently replaced by a real estimate without the nearest-integer identity.',
    'ACTUAL integer polynomial evaluation divisibility proves R(a+M*q*t)-R(a)=q*k for an actual integer k. True integer division gives R(n)=m/M+q*k, with 0<=m<M*q. Positive ORIGINAL lattice power Exp(y)^q supplies genuine original right-coset period and finite representatives Exp((m/M)*y). Exp(y) itself is NOT assumed lattice, and arbitrary right translation on original quotient is NOT assumed.',
    'ACTUAL error variation is PROVED: M*abs(E(x)-E(t)) <= (j+1)^2*B*H/N when abs(x),abs(t)<=N and abs(x-t)<=H. Its actual value is <=(j+1)^2*B. This is a bounded error with short-interval variation, NOT globally small error or a large child correlation. Actual one-parameter exponential identities split original real samples EXACTLY as epsilon(t)*gamma(t)*gK(t), with genuine K weights and original degree.',
    'SAME original nonzero terminal Fourier signal now yields FULL original inverse OR the genuine strictly smaller rational kernel filtration, COMPLETE Q tables, P higher tables/P(1), actual small/rational factors, error variation, finite original lattice residues and true periods. The common positive multiplier is bounded BEFORE p/N, and SAME dense useful V retains BOTH original-scale relative/bracket bounds. All geometry, universal exact source factorization and original horizontal inverse branch are retained. General degree has ONLY FULL lower-degree inverse premise; degree TWO has NO child inverse premise.'
]
remaining='''StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Full positive distinct rapidly separated monochromatic finite sums/products remains the prize target. Existing native geometry, degree recursion, corrected scalar/bracket inverse, original-vector/integral-commutator/zero-difference branches, true rational nonlinearity kernel and strict natural nonlinearity drop are retained. SAME remaining Fourier signal now yields genuine complete native Q tables from TWO at a true common positive bounded multiplier, actual higher P tables/P(1), exact raw Q_F high-coefficient identities and genuine nearest-integer small/rational decomposition along the actual highest rational direction y. Actual rational scalar periods, finite ORIGINAL lattice right-coset representatives and actual error variation/value bounds are proved. Exact real source samples are epsilon*gamma*gK with true K weights/degree. Correlation transfer has NOT been inferred: rational gamma is LEFT of gK, so its right-coset residues cannot directly replace it inside the original product. Need actual rational-conjugated source, true K weights after coefficient collection, finite simultaneous geometry/period budgets, correct conjugated-lattice right-quotient homeomorphism/native data/Haar/unit-observable transport, actual short residue progression with large child correlation and original-scale length/coefficient comparison. Only then apply genuine degree+nonlinearity induction. P first coefficient/full diagonal alternative, full original inverse all small-N source branches, corrected multivariate inverse, separate interval Gowers correlation inverse, rough progressions, cube/Alignment and StrongConjecture remain OPEN. Bounds are fixed-data existential constants, NOT explicit delta-power laws. Positive exponential lattice powers are proved; Exp(y) itself is not declared lattice. Author build/hash/axiom/source review is NOT independent kernel replay or external peer review. The repaired source slab estimate is NOT an unavoidable obstruction. Public repository/PR/prize milestone has NOT been reached.'''
text=Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
    text=re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),text,flags=re.M)
text=re.sub(r'^"""Audit .*?\n','"""Audit complete native nonlinear tables and actual small/rational source factors.\n',text,count=1)
text=re.sub(r"reference_scope='[^']*'", "reference_scope='OpenAI quantitative Leibman route; SAME native signal, complete Q second coefficient, actual small/rational factors and original lattice periods; conjugated-source/correlation transport and full target remain open'",text)
Path(prefix+'-audit.py').write_text(text,encoding='utf-8')
review='''JSP-000168 / Erdos #172: complete Q tables and genuine small/rational factors
Author mathematical review, 2026-10-13. Verdict: Partial coverage.
Previous retained registered goal round: PROGRESS.
NOT independent kernel replay or external peer review.
Full original positive distinct monochromatic FS/FP remains OPEN.
Pinned OpenAI six-section source:
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
06_rough_progressions.tex, quantitative Leibman route.
Auxiliary primary source: https://arxiv.org/html/0709.3562v4
Corrected multivariate scope: https://arxiv.org/html/1311.6170v3

1. Missing second coefficient is genuinely recovered
Zero actual original commutator pairing sets ALL bracket zeta_i to zero,
so retained native bracket is exactly beta+alpha*h, beta=M*P(1),
alpha=M*Q_bin2. Actual V subset range N and density min(rho,1) transport
into the proved affine inverse with epsilon=B/N. Threshold includes true
ceil(10*B/density). Positive bounded r therefore controls N^2*norm(r*alpha)
and N*norm(r*beta) at original N. These constants precede all raw sources.
Multiply every retained higher table by r, then use actual quadratic
remainder Q_bin2-2*Q_mono2. Triangle inequality controls 2*r*M*Q_mono2;
absorb genuine positive factor two into the SAME multiplier M_new. Higher
Q monomial bounds and actual monomial/binomial conversion complete BOTH
Q tables for EVERY degree >=2. BOTH higher P tables and P(1) survive.
No cancellation from independently selected multipliers is assumed.
P first coefficient/full diagonal alternative remains a separate task.

2. Exact native Q versus raw removed nonlinear part
Real restriction F|F_2=psi and actual submodule scalar projection identify
the nonlinear F_2 polynomial scalar. Native linear step subtracts exactly
x times F(a). Actual compact normalizations add/subtract only affine
terms under true original horizontal logarithmic character. Hence ALL
monomial coefficients >=2 of compact Q equal raw F(p), exactly. Q_F
removes the actual raw constant/linear coefficients, so the same high
coefficients agree. Higher binomial coefficients depend only on monomial
coefficients >=their index, giving exact agreement from degree two.
Full Q=Q_F is NOT claimed: native Q(1)=0 and raw affine removal differ.

3. True real error and integer numerator
Set z_i=round(M*Q_F.coeff i) and define R=sum_{i=2..j}(z_i/M)*X^i.
Prove its actual coefficients, degree bound and identity as M^-1 times
the mapped integer polynomial numerator. E=Q_F-R has degree <=j and
coefficients zero at 0,1. Exact norm identity for nearest integers gives
M*abs(E.coeff i)=norm(M*Q_F.coeff i mod one), so every original N^i bound
becomes a REAL coefficient bound. Positivity M is used for true division;
there is no assumed real-small coefficient from circle norm alone.
Numerators may be arbitrarily large and are never declared bounded.

4. Actual periods and finite original lattice residues
Integer-polynomial evaluation satisfies a-b divides Z(a)-Z(b). Since
M*q divides the true progression step M*q*t, integer divisibility and
division by positive M prove R(a+M*q*t)-R(a)=q*k. Genuine Euclidean
division of Z(n) modulo positive M*q yields m<M*q and R(n)=m/M+q*k.
True Exp(c*y) one-parameter multiplication/int-power identities plus
Exp(y)^q in ORIGINAL Gamma prove EXACT original right-coset equalities.
Exp(y) itself is NOT asserted in Gamma. Family has M*q representatives;
q is actual geometry, not an additional assumed universal complexity.
Uniform finite geometry/period-budget selection remains to be coupled
to the analytic induction before claiming fully bounded child complexity.

5. Variation and correct product order
The actual normalized power variation bound and finite coefficient sum
prove M*abs(E(x)-E(t)) <= (j+1)^2*B*(H/N) for abs(x),abs(t)<=N,
abs(x-t)<=H. Since E(0)=0 and M>=1, actual value is <=(j+1)^2*B.
This is not uniformly tiny: short intervals are still needed to freeze it.
True Exp addition along SAME y splits actual raw samples as
 g_p(t)=Exp(E(t)*y)*Exp(R(t)*y)*gK(t)
for ALL real t, with actual weighted K source pK of degree ell.
The genuine group order is epsilon*gamma*gK. Right-coset periodicity of
gamma ALONE cannot replace gamma by a finite representative to the LEFT
of variable gK. This is not treated as child nonuniformity.

6. Same original signal composition
Before p/N choose complete-table budgets using old fixed A,S,rho. Enlarge
threshold and coefficient bound once. Apply original Fourier packet;
FULL original horizontal/grid/nonzero/coefficient branch is unchanged.
Remaining branch keeps actual chi in same finite C, same offset b,
same original V, all positive/range/density data and relative tables.
New bounded positive common M provides complete Q tables and P(1).
Actual affine completion N*norm(beta+alpha*h)<=2*A from N*norm(beta)<=A,
N^2*norm(alpha)<=A for h<=N restores the SAME native bracket at NEW M.
Actual canonical K, strict F_2 dimension/nonlinearity drops, highest rational
y with F(y)=1, killed next layer and positive original lattice power are
retained. Actual small/rational factors, real error bounds, original finite
residues/periods and universal exact source factorization are composed.
General ell retains ONLY full lower-degree inverse premise. Degree two
uses proved degree-one base, with NO child inverse premise. Neither is
the full original inverse or a proof of the final prize statement.

7. Remaining mathematical obligations
Construct actual rational conjugate gK'=gamma*gK*gamma^-1, keeping old
weights via actual native products/highest-layer direction. Actual F
conjugation invariance leaves affine projection; true aggregate collection
and zero trimming must then certify actual K weights and original degree.
Rewrite g=epsilon*gK'*gamma before using finite gamma right cosets.
Use Gamma_rho=rho*Gamma*rho^-1 and the ACTUAL homeomorphism
G/Gamma_rho -> G/Gamma, x -> x*rho. Arbitrary right translation on the
original quotient is NOT available. Prove actual native data, topology,
metric/Haar/unit-observable transports, including zero mean of the actual
nonzero terminal Fourier signal. Select actual short residue progressions
with large child correlation and length >=tau*N; account for actual error
freezing and original-scale source coefficient conversion.
Then prove true well-founded degree+nonlinearity induction and BOTH full
raw original coefficient tables. Full original inverse small-N branches,
corrected multivariate inverse, separate interval Gowers correlation inverse,
rough progressions, cube/Alignment and StrongConjecture remain OPEN.
No unavoidable obstruction found; public repository/PR/prize not triggered.
Fixed-data existence does not certify source explicit delta-power laws.

All retained registered Lean hashes and selected axiom sets must remain
unchanged. Every new source requires explicit autoImplicit=false EMPTY
logs, terminal full build and expanded standard-only axiom audit. No new
axiom/sorry/admit/oracle/custom structure, unsafe/native_decide or option
bypass. Re-execute the exact rational slab certificate and pin/hash the
six original OpenAI sections and Lean/mathlib/PNT+ revisions.
'''
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
print(json.dumps(dict(prefix=prefix,modules=modules)))
