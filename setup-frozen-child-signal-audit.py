from pathlib import Path
import json
import re

prefix='round-native-rational-frozen-child-signal'
old='round-native-rational-conjugate-right-factors'
base=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained={f['path'] for f in base['files']}
modules=sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules)==19,modules
components=[
    'ACTUAL COMPLEX original terminal Fourier signal has a PROVED uniform scalar LEFT-action modulus on bounded real parameters BEFORE every raw polynomial/sample. Genuine compact original quotient times actual compact UNIT observable subtype, original Fourier function-space continuity and true continuous evaluation/action supply the modulus. No spatial Lipschitz Fourier projection or uniformly spatially Lipschitz action is assumed.',
    'TRUE original REAL error coefficient/value/variation bounds now prove genuine COMPLEX signal freezing on a fixed positive fractional short interval. Radius precedes ALL raw E/M/N/samples. Actual right-ordered group identity and original right-coset residue equality PROVE actual approximation by the genuine frozen observable on TRUE conjugated native data, with correct group order and original samples.',
    'An ACTUAL finite complex sample partition has a NONEMPTY fiber mean norm at least the original mean norm, using TRUE cardinal weights and exact finite fiber sums. Genuine balanced interval/residue partition of ALL original 0<=n<N samples yields a true large cell with length>=N/(4*K*period) once N>=4*K*period. True original range/short-distance/congruence are PROVED. No equal cell size, phase alignment or discarded-tail signal is assumed.',
    'ACTUAL integer polynomial divisibility proves the rational-factor original right coset CONSTANT for ANY two congruent original integer inputs, including negative differences. Real error freezing on the selected true cell and actual complex finite-mean error stability PROVE a GENUINELY LARGE frozen child mean >delta/2 and ZERO child canonical Haar mean, with a TRUE finite rational representative and original-scale cell length.',
    'ACTUAL original residue cell is EXACTLY one affine image of standard integer interval 0<=t<T, with exact cardinal/mean and no endpoint loss. Genuine affine source substitution keeps TRUE smaller-filtration weights and original degree. Exact child native samples, actual conjugated rational filtration, strict same-degree nonlinearity loss and GENUINE large standard-progression mean are PROVED, with TRUE original-scale length and bounded frozen scalar.',
    'An ACTUAL compact continuous-observable family on genuine native data has one fixed finite UNIT-Lipschitz discrepancy detector, by true compact finite Lipschitz approximation, exact normalization and actual discrepancy norm/error bounds. Actual nonzero original frozen Fourier family uses PROVED ZERO canonical Haar mean to turn the large frozen mean into discrepancy. A TRUE finite representative pool over ALL 0<M<=S, m<M*q gives ONE positive threshold BEFORE every raw source/sample/error, using actual finite minimum and true compact scalar LEFT family.',
    'For ACTUAL fixed nonzero-difference/zero-pairing character, highest rational j/y/positive lattice power q, block K and ONE positive UNIT threshold are selected BEFORE every bounded M/raw p/N. Actual COMPLETE native Q coefficient bounds plus SAME original Fourier signal yield a TRUE smaller-rational-filtration source on a standard child Unit cube with GENUINELY LARGE UNIT-observable canonical discrepancy. Threshold N>=4*K*S*q and length>=N/(4*K*S*q) are fixed before all sources. Child has SAME layers as original true kernel and STRICT natural nonlinearity loss. ACTUAL error/rational source factors and exact affine child sample relation are RETAINED for future original-coefficient transport. No same-degree child inverse is assumed.'
]
remaining='''StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Full original positive distinct rapidly separated monochromatic finite sums/products remains the prize target. All prior native geometry/inverse branches, complete Q second tables, small/rational/right factors, genuine rational kernel/nonlinearity descent, correct conjugated native/Haar/observable/character transport are retained. ACTUAL COMPLEX original Fourier freezing, true balanced interval/residue complex-mean selection, constant integer rational-factor right coset, REAL freezing errors and exact standard-progression enumeration now PROVE GENUINELY LARGE zero-Haar-mean child signal with original-scale length. True affine source weights/degree/strict smaller nonlinearity and actual compact-family UNIT detection are PROVED. Finite representative pool over bounded positive M and fixed q has ONE positive threshold BEFORE all raw samples. For each ACTUAL fixed valid relative character, highest j/y/q and block/UNIT threshold precede all M/p/N: true complete Q bounds and SAME original Fourier signal give genuine standard child Unit-cube discrepancy >theta, true smaller source, length>=N/(4*K*S*q), and retained exact source factor/progression relationships. Full same-degree inverse is NOT yet proved. Remaining: finite simultaneous geometry/threshold budgeting over the original finite CHARACTER pool and explicit composition with all original native Fourier branches; actual child-character progression/translation/length/rational-denominator/REAL-error coefficient transport back to BOTH COMPLETE raw ORIGINAL tables; genuine well-founded degree+nonlinearity induction and all original small-N cases. P first/full diagonal alternative, corrected multivariate inverse, separate interval Gowers correlation inverse, rough progressions, cube/Alignment and final StrongConjecture remain OPEN. Fixed-data existential bounds are NOT explicit delta-power laws. Only true positive exponential lattice powers are asserted, not Exp(y) lattice membership. Author build/hash/axiom/source review is NOT independent kernel replay or external peer review. Repaired source slab estimate is NOT an unavoidable obstruction. Public repository/PR/prize milestone has NOT been reached.'''
text=Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
    text=re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),text,flags=re.M)
text=re.sub(r'^"""Audit .*?\n','"""Audit actual complex freezing, genuine short progression and smaller-filtration UNIT child signal.\n',text,count=1)
text=re.sub(r"reference_scope='[^']*'", "reference_scope='OpenAI quantitative Leibman route; actual complex freezing, original-scale short residue progression and genuine smaller-filtration Unit-cube signal; full character-pool/source-coefficient induction and final target remain open'",text)
Path(prefix+'-audit.py').write_text(text,encoding='utf-8')
review='''JSP-000168 / Erdos #172: GENUINE frozen progression / child UNIT signal
Author mathematical review, 2026-10-13. Verdict: Partial coverage.
Previous retained registered goal round: PROGRESS.
NOT independent kernel replay or external peer review.
Full original positive distinct monochromatic FS/FP remains OPEN.
Pinned OpenAI six-section source:
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
06_rough_progressions.tex, quantitative Leibman route.
Auxiliary primary source: https://arxiv.org/html/0709.3562v4
Corrected multivariate scope: https://arxiv.org/html/1311.6170v3

1. Genuine COMPLEX original Fourier freezing
Original specified metric quotient is ACTUALLY compact. Original unit
continuous-observable subtype has actual induced metric and PROVED compact
space instance. Define X=original quotient times this actual unit subtype.
Define f(a,(x,F))=Phi_k(F)(Exp(a*y) LEFT-action x). Actual original Fourier
function-space continuity, native scalar action continuity and continuous
evaluation PROVE f continuous. Apply PROVED compact parameter modulus on
[-B,B] times X with COMPLEX codomain and epsilon/2. This yields true positive
scalar radius before every F/raw polynomial/sample. Distance in C is true
complex difference norm. No spatial Lipschitz of Phi_k(F) or group action
is inferred from original unit F; genuine compactness supplies the modulus.

2. REAL error bound -> actual frozen sample error
Actual E has degree<=j, coefficients zero at 0,1 and real coefficient bound
M*N^i*abs(E_i)<=A. PROVED scalar error value/variation give bounded values
B=(j+1)^2*A and M*abs(E(x)-E(b))<=B*(H/N). M>=1 is used. Choose r=min(1,
eta/(B+1))>0 before E/M/N. With abs(x-b)<=r*N, actual variation is <=eta,
so true complex signal difference is <epsilon. E is not globally tiny.

Given ACTUAL g=Exp(E(x)*y)*h*gamma and true gamma Gamma=rho Gamma, original
LEFT action yields ACTUAL whole-sample right representative rho. True
frozen conjugated observable evaluates as Phi_k(F)([Exp(E(b)*y)*h*rho]).
Hence actual error is <epsilon in correct group order. No arbitrary
right action on original nonnormal quotient is asserted.

3. Actual balanced complex residue partition
For true finite original sample set S, label fibers give exact sum and
exact total cardinal weights. Select maximum actual fiber mean norm over
actual nonempty image of labels. Norm triangle and true weights show that
its NONEMPTY fiber mean is >=original mean. Fibers need not have equal
sizes; no phase alignment between different complex means is assumed.

Label each original integer 0<=n<N by ACTUAL balanced interval label and
true modulo-P representative. Fiber equals actual interval residue set.
True balanced cut lower width>=N/(2*K), residue count error<=1 and
N>=4*K*P give ACTUAL cell cardinal >=N/(4*K*P). Original containment,
distance<=2*N/K and original integer congruence are PROVED. This partitions
ALL original samples without an assumed boundary/tail contribution.

4. Real period, finite representative and genuine large frozen mean
Extend true integer-numerator divisibility to ANY congruent integer inputs
a,n, not only naturals a+period*t. M*q divides n-a and therefore divides
Z(n)-Z(a); division by true positive M gives R(n)-R(a)=q*k with actual
integer k. True one-parameter Exp multiplication/int-power and actual
Exp(y)^q in ORIGINAL Gamma prove CONSTANT original right coset on each
actual selected cell. Negative differences are allowed and handled by
true integer powers. Exp(y) itself is not assumed lattice.

Select actual large cell, actual anchor a in it, finite representative m
from gamma(a) and true period M*q. Anchor is in ORIGINAL 0<=a<N, so true
integer-to-natural transport is applied to the finite-representative lemma.
Choose block K=ceil(2/r)+1 before ALL E/M/q/N; cell distance<=r*N. True
coefficient freezing supplies complex error<delta/4 for every sample.
Actual finite mean error bound and true original cell mean>=delta imply
frozen child mean>delta/2. Actual frozen conjugate Fourier ZERO Haar mean
is retained. This is GENUINE child nonuniformity, not an added hypothesis.

5. Exact progression / genuine smaller source
Use actual residue coordinate endpoints U,V. TRUE interval residue set
equals affine image b+P*[U,V). Translation by U gives EXACT standard
integer interval [0,T), T=(V-U).toNat, with actual cardinal T and exact
complex mean. There is no endpoint loss. Actual start a belongs to the
selected original cell and 0<=a<N; true T>0 and original-scale lower bound
come from actual cell cardinal. Affine source pNew=pK(a+P*t) is CONSTRUCTED.
PROVED affine degree and weights preserve actual smaller rational filtration
and original ell. Actual conjugated residue filtration has SAME kernel
layers and strict original natural nonlinearity loss. Exact child native
sample equality and actual standard-progression large mean are PROVED.
Frozen scalar c=E(anchor) is genuinely bounded by (j+1)^2*A.

6. Actual UNIT detection with uniform finite residue budget
For actual compact continuous-observable family on native D, apply PROVED
finite bounded spatial Lipschitz approximation at delta/8. True discrepancy
linear norm<=2 and approximation error give approximant signal>delta/2.
Actual scale R=1+B+L normalizes a TRUE finite list into unit observables,
with positive detector threshold before all sample sets/orbits. This is
not an inverse theorem. Canonical frozen nonzero Fourier ZERO Haar mean
turns actual frozen mean into actual discrepancy on conjugated native data.

For true S>0,q>0 and fixed y, use actual finite pool Fin(S) x Fin(S*q),
denominator M=i+1 and numerator m. It covers EVERY 0<M<=S, m<M*q.
Even extra pool numerators are legitimate conjugated native data; no fake
period property is needed for them. Actual compact scalar LEFT family is
image of [-B,B] under Exp(c*y). Choose detector for every actual pool member,
then take TRUE finite positive minimum. ONE positive threshold therefore
precedes ALL raw E/M/N/samples/frozen scalars. Sampling universe is explicit
and consistent in dependent finite choice. No vanishing threshold or source-
dependent constants are silently called uniform.

7. Actual fixed-character nonlinear branch -> genuine child UNIT cube
For actual valid relative chi with nonzero difference / zero pairing, apply
PROVED rational nonlinearity exact factorization to select actual highest
j,y,q and strict kernel drop BEFORE all raw sources. Choose block and ONE
unit threshold over ALL 0<M<=S and finite representatives before p/N.
ACTUAL complete Q monomial bounds feed PROVED nearest-integer/right-factor
construction; its TRUE K-weighted source and real coefficients feed actual
freezing/partition/progression/unit detection. ORIGINAL Fourier signal is
the same input; actual child mean is derived, never assumed. Exact standard
integer interval/Unit cube discrepancy equality gives GENUINE child UNIT
canonical discrepancy >theta, with TRUE smaller source weights/original
degree and strict actual nonlinearity loss.

Original threshold N>=4*K*S*q and child length>=N/(4*K*S*q) are fixed
before every source, using ACTUAL M<=S. Every finite child lattice comes
from genuine Exp((m/M)*y), with same kernel layers. Actual real E coefficients,
integer rational numerator, original ALL-real source factorization and exact
affine child sample relation are RETAINED in the theorem output. This is
essential for future character/coefficient transport; no unrelated child
orbit or discarded source relation is substituted for the original target.
Retained child sample equality is an ACTUAL coset equality at EVERY integer
input. It is not a claimed arbitrary-vector/group equality; use actual
horizontal integrality or a stronger constructor theorem when transporting
scalar coefficients. Original factor identity is genuinely ALL-real group equality.
NO same-degree child inverse is assumed, and the full inverse is not claimed.

8. Remaining full-goal proof obligations
Uniformly budget the highest-direction/power/block/threshold choices over
the ORIGINAL finite actual CHARACTER pool (good subset only), then compose
with ALL original native Fourier branches and full original character
reconstructions. Fixed-chi geometry before p is proved; global finite-chi
budget composition is still required. Apply genuine well-founded degree+
nonlinearity induction with the ACTUAL child signal now available. Transport
actual child character across genuine conjugation, original progression
translation/step and length, actual rational denominator clearing and REAL
error coefficient bounds to BOTH COMPLETE raw ORIGINAL tables. Existing
horizontal/grid transport alone does not certify original coefficient tables.
Complete original inverse all small-N source branches and P first/full
diagonal alternative as needed. Corrected multivariate inverse, separate
interval Gowers correlation inverse, rough progressions, cube/Alignment and
final positive distinct rapidly separated FS/FP remain OPEN. No unavoidable
obstruction found; public repository/PR/prize milestone has NOT been reached.
Fixed-data existence does not certify source explicit delta-power laws.

ALL old registered Lean hashes/selected axiom sets retained. Require every
new module explicit autoImplicit=false EMPTY log, terminal full build and
expanded standard-only axiom audit. No custom axiom/sorry/admit/oracle data
structure, unsafe/native_decide or option bypass. Re-execute exact rational
slab certificate and pin/hash all six original OpenAI source sections plus
Lean/mathlib/PNT+ revisions. Author checking is not independent kernel replay
or external peer review.
'''
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
print(json.dumps(dict(prefix=prefix,modules=modules)))
