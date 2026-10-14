from pathlib import Path
import json

prefix='round-native-rational-small-rational-factors'
review=json.loads(Path(prefix+'-review.json').read_text(encoding='utf-8'))
manifest=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
assert manifest['last_round']['review_file']==prefix+'-review.json'
s=review['verified']
assert not s['full_target_proved']
status=f'''JSP-000168 / Erdos #172 -- 2026-10-13

Goal ACTIVE; StrongConjecture UNPROVED; no unavoidable obstruction found.
Verdict: Partial coverage. Previous goal round and this round: PROGRESS.
Latest audit: {prefix}
{len(review['new_modules'])} new modules, {s['new_theorems']} new theorems,
{s['new_definitions']} definitions. Verification awaited terminal success.

NOW PROVED:
'''+ '\n'.join('* '+c for c in review['application_review'][:-1])
status+=f'''

VERIFIED:
{s['project_modules']} own modules, {s['pntplus_modules']} attributed PNT+ modules;
{s['build_jobs']} full-build jobs, {s['selected_axiom_reports']} selected axiom reports.
Every new source passes explicit -DautoImplicit=false with EMPTY logs.
All retained registered proof hashes and selected axiom sets unchanged.
Only root/import and axiom registry changed. Standard axioms only. Pinned
Lean/mathlib/PNT+ and all six original OpenAI sections rechecked.
Author checking is NOT independent kernel replay or external peer review.
The exact rational slab certificate was re-executed and arithmetic/hash
checked; its repaired source estimate is not an unavoidable obstruction.

CURRENT EXACT SCOPE:
The missing native Q second coefficient is PROVED from SAME dense affine
bracket samples under actual zero commutator pairing. One common actual
positive bounded multiplier controls BOTH COMPLETE Q monomial/binomial
tables from TWO, BOTH higher P tables and P(1) at original N.
The same V/relative bounds and actual bracket at NEW multiplier are retained.

Actual native Q and the raw removed nonlinear scalar Q_F have EXACTLY the
same every high coefficient. They are not identified as whole polynomials.
Nearest integers give genuine Q_F=E+R with one true positive denominator,
actual integer numerator and REAL error bounds M*N^i*abs(coeff_i E)<=A.
Actual integer divisibility/Euclidean division give true R progression
periods and finite ORIGINAL lattice right-coset representatives. Only
positive Exp(y)^q lattice power is required, not Exp(y) itself.

Exact original real samples satisfy g=epsilon*gamma*gK, with TRUE weighted
K source of degree ell. Actual error variation is <=(j+1)^2*A*H/(M*N)
and value <=(j+1)^2*A on abs(t)<=N. Value is bounded, not globally tiny.
The SAME original Fourier signal returns full original inverse OR all
this actual data plus strict rational nonlinearity drop. General degree
has ONLY full lower-degree inverse premise; degree-two version has NO
child inverse premise. This is not yet the full inverse or final FS/FP.

NOT YET PROVED:
Rational gamma stands LEFT of gK, so right-coset periodicity of gamma ALONE
does not allow its replacement inside the original product. Need genuine
conjugated source gK'=gamma*gK*gamma^-1, preserving actual K weights,
and g=epsilon*gK'*gamma. Then use conjugated lattice Gamma_rho and a true
right-quotient homeomorphism, not arbitrary right action on G/Gamma.
Actual native data/Haar/unit observable/large-correlation transports,
finite geometry/period budgets, short progressions and length/coefficient
comparison are OPEN. Complete degree+nonlinearity induction remains OPEN.

NEXT:
See FACTORIZATION-CORRELATION-CONTINUATION.txt (completed stages 1--4;
remaining conjugation/quotient/correlation plan is NOT a proof).
See CONJUGATE-SOURCE-CONTINUATION.txt for concrete existing helper names
and actual source/right-quotient/Haar/analytic obligations (PLAN ONLY).
Return BOTH full original raw coefficient tables; finish P first/diagonal
alternative and all small-N original inverse cases. Corrected multivariate
inverse, separate interval Gowers correlation inverse, rough progressions,
cube/Alignment and StrongConjecture remain OPEN. Fixed-data existential
constants do not establish source explicit delta-power complexity.

PUBLICATION:
No public repository, PR or prize application yet. User milestone is full
formalization or genuine unavoidable obstruction; neither has been reached.

FULL REMAINING SCOPE:
'''+review['remaining']+'\n'
Path('CURRENT-STATUS.txt').write_text(status,encoding='utf-8')
with Path('CONTINUATION.txt').open('a',encoding='utf-8') as stream:
    stream.write('\n\n2026-10-13 LATEST GOAL ROUND: '+prefix+'\n'+status)
Path('NONLINEARITY-CONTINUATION.txt').write_text(
    'COMPLETED geometry / exact factorization / native second coefficient and actual small-rational split, 2026-10-13.\n'
    'True rational kernel, strict natural nonlinearity drop, constructed K source and exact real factors are proved.\n'
    'Complete Q tables, real error coefficients, original lattice periods/finite residues and actual error variation are proved.\n'
    'Conjugated K source / true quotient-Haar-observable / child correlation remain OPEN.\n'
    'See CURRENT-STATUS.txt, '+prefix+'-mathematical-review.txt and FACTORIZATION-CORRELATION-CONTINUATION.txt.\n',encoding='utf-8')
guide=Path('FACTORIZATION-CORRELATION-CONTINUATION.txt').read_text(encoding='utf-8')
marker='2026-10-13 SMALL/RATIONAL FACTOR MILESTONE COMPLETED'
if marker not in guide:
    guide=marker+''' in author-audited Lean state.
Concrete stages 1 (true Q second), 2 (raw high-coefficient identities),
3 (nearest-integer real/rational split), 4 (actual periods/finite original
right-coset residues), and ERROR VARIATION part of stage 7 are now PROVED.
All original dense V/relative/bracket data survive at the NEW common
positive multiplier. See actual new NativeRationalDenseSmallRationalFactors
and NativeRationalDegreeTwoDenseSmallRationalFactors theorems and latest
mathematical review. P first/full diagonal alternative is still open.

NEXT is stage 5 actual conjugated K source, then stage 6 actual correct
quotient/native-data/Haar/unit observable transport, remaining stage 7
actual large-correlation short progression, stage 8 complete induction.
Finite simultaneous geometry/period budgets need actual selection.
No child nonuniformity is obtained from coset identities alone.
Below is the retained earlier PLAN for context. Completed proof references
supersede its old open-status descriptions for stages 1--4 / variation.
Remaining plan is NOT a proof. Goal ACTIVE; no unavoidable blocker.

'''+guide
    Path('FACTORIZATION-CORRELATION-CONTINUATION.txt').write_text(guide,encoding='utf-8')
print(json.dumps(s))
