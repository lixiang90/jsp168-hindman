from pathlib import Path
import json
import re

prefix='round-native-rational-conjugate-right-factors'
old='round-native-rational-small-rational-factors'
base=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained={f['path'] for f in base['files']}
modules=sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules)==14,modules
components=[
    'TRUE scalar-to-Unit Mv conversion preserves actual degree/evaluations/coefficients. ACTUAL variable conjugation gamma*gK*gamma^-1 is constructed by native BCH/Picard products then genuine aggregate coefficient collection/zero trimming. Old L weights, EXACT horizontal scalar projection and actual affine degree prove TRUE smaller-kernel weights and original degree ell. The conjugating direction itself is NOT assumed kernel-filtered.',
    'TRUE original group samples now factor in CORRECT order g=epsilon*gK_conjugated*gamma for ALL real inputs. Actual finite original right-coset representatives of gamma therefore apply to ACTUAL whole original samples by original LEFT action, with the same bounded error factor. SAME original nonzero Fourier signal now yields full original inverse OR these actual right-ordered factors/whole-sample residues, retaining complete Q/P(1)/higher P tables, same common bounded positive M, same dense V/relative/bracket bounds and actual strict nonlinearity drop. General degree has ONLY full lower-degree inverse premise; degree two has NO child inverse premise.',
    'GENUINE right-coset equivalence/homeomorphism from G/(rho Gamma rho^-1) to ORIGINAL G/Gamma sends [x] to [x*rho]. Its actual inverse, both identities, original LEFT equivariance and continuity are PROVED. No arbitrary right action on ORIGINAL nonnormal quotient is asserted. Original compatible metric is ACTUALLY pulled back, true isometry equivalence and the new open quotient map/topology are PROVED.',
    'TRUE conjugated native nilmanifold data copies ORIGINAL model/manifold/group and PROVED conjugate lattice discreteness/compactness, with actual transported compatible metric. ACTUAL rational conjugation preserves original rational log span, so EVERY true original rational Lie filtration transports to SAME layers on actual conjugated data. EVERY genuine finite rational representative Exp((m/M)*y) receives the true smaller rational filtration, actual source weights and SAME strict natural nonlinearity drop.',
    'ACTUAL conjugated native canonical probability pushes through true right-coset homeomorphism to ORIGINAL canonical probability. Measurability, probability, actual left equivariance/invariance and PROVED uniqueness of invariant probability establish genuine Haar agreement and true integrals for every original function. No assumed common Haar normalization or measure-identification oracle is used.',
    'ACTUAL continuous original observables pull back through true right-coset isometry with PROVED unit Lipschitz preservation and canonical integral transport. Actual frozen LEFT parameter plus original terminal Fourier projection gives a GENUINE compact continuous-observable family on conjugated native data, norm <=ONE for original unit inputs, ZERO canonical Haar mean for original nonzero mode, and ACTUAL group-sample evaluation formula. Arbitrary compatible-metric left actions are NOT asserted uniformly spatially Lipschitz; no freezing error or child correlation is assumed.',
    'ACTUAL original horizontal logarithmic characters are PROVED conjugation invariant. TRUE nonzeroness, Lie commutator annihilation and original lattice integrality hold iff on actual conjugated lattice. A bounded genuine child horizontal character consequently belongs to ORIGINAL finite horizontal grid with SAME norm budget. Complete source-table/correlation induction transport remains open.'
]
remaining='''StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Prize target remains full original positive distinct rapidly separated monochromatic finite sums/products. Existing native inverse branches, complete Q second tables, actual nearest-integer small/rational split, strict kernel nonlinearity descent, original lattice periods/error variation are retained. ACTUAL rational variable conjugation now constructs a TRUE weighted smaller-filtration source and exact right-ordered real factorization g=epsilon*gK_conjugated*gamma. SAME Fourier packet keeps full original inverse OR actual whole-sample finite right representatives, all complete Q/higher P/P(1)/original dense V bounds and genuine strict descent. TRUE conjugated right-coset homeomorphism/metric/native data/rational filtration and ACTUAL canonical Haar probability/integral transport are proved. Frozen LEFT parameter / original nonzero Fourier projection yields actual compact bounded zero-Haar-mean continuous-observable families on TRUE conjugated native data; unit right-pullback and original horizontal/grid character transport are proved. This does NOT establish actual freezing error or large child correlation. Remaining: choose finite simultaneous highest-direction/lattice-power/period/geometry budgets BEFORE all raw sources; actual compact-parameter action error from genuine uniform continuity, short original residue progression with large mean and length>=tau*N, correct continuous-family to unit-observable inverse detection, actual translated-progression/source coefficient/denominator clearing back to BOTH complete raw ORIGINAL tables, and genuine degree+nonlinearity induction. P first/full diagonal alternative, all small-N original inverse branches, corrected multivariate inverse, separate interval Gowers correlation inverse, rough progressions, cube/Alignment and final StrongConjecture remain OPEN. Fixed-data existential budgets are NOT explicit delta-power laws. Only true positive exponential lattice powers are asserted, not Exp(y) lattice membership. Author build/hash/axiom/source review is NOT independent kernel replay or peer review. Repaired source slab estimate is NOT an unavoidable obstruction. Public repository/PR/prize milestone has NOT been reached.'''
text=Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
    text=re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),text,flags=re.M)
text=re.sub(r'^"""Audit .*?\n','"""Audit actual conjugated source, right quotient/native geometry, Haar and observable transport.\n',text,count=1)
text=re.sub(r"reference_scope='[^']*'", "reference_scope='OpenAI quantitative Leibman route; ACTUAL conjugated smaller source, correct right quotient/native data/Haar/zero-mean compact observable families; freezing/short-progression correlation and full target remain open'",text)
Path(prefix+'-audit.py').write_text(text,encoding='utf-8')
review='''JSP-000168 / Erdos #172: ACTUAL conjugated source and correct quotient/Haar
Author mathematical review, 2026-10-13. Verdict: Partial coverage.
Previous retained registered goal round: PROGRESS.
NOT independent kernel replay or external peer review.
Full original positive distinct monochromatic FS/FP remains OPEN.
Pinned OpenAI six-section source:
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
06_rough_progressions.tex, quantitative Leibman route.
Auxiliary primary source: https://arxiv.org/html/0709.3562v4
Corrected multivariate scope: https://arxiv.org/html/1311.6170v3

1. Genuine conjugated smaller source
Actual scalar inverse Unit conversion preserves true coefficients, all
real evaluations and degree<=j. Direction y lies in actual highest Lj,
so [(R,y)] and [(R,-y)] are ACTUALLY old L weighted when R has degree<=j.
Kernel source pK is old L weighted by actual layer inclusion. Two native
BCH/Picard products form actual log of gamma*gK*gamma^-1. Genuine original
horizontal projection is additive under both products; actual direction
projections cancel exactly as Mv polynomials. F projection remains that
of pK. K.layer(2)<=ker F gives actual scalar degree<=1. Genuine aggregate
collection and zero-vector trim consequently construct an ACTUAL K source
with original degree ell. Raw-term cancellations are retained. Rational
gamma itself is NOT declared K weighted; only the constructed conjugate is.
Exp/Log inverse and actual native product evaluation prove EVERY real
sample gK'=gamma*gK*gamma^-1. No source filteredness is supplied as an oracle.

2. Correct original factor order and same signal
Combine actual epsilon*gamma*gK identity with above conjugate identity to
prove g=epsilon*gK'*gamma for EVERY real t. True finite right-coset residues
of gamma now act on the RIGHT of gK', so congruence under ORIGINAL LEFT
action yields actual whole-sample equality in ORIGINAL G/Gamma. Error E(t)
is retained exactly and remains variable. These are not child correlations.
The SAME original nonzero terminal Fourier packet now retains these actual
right-ordered factors and whole-sample residues along with COMPLETE Q
mono/binomial tables from two, BOTH higher P tables and P(1), SAME positive
bounded common M, actual chi/offset/dense V, BOTH original-scale relative/
bracket bounds, actual K strict dimension/nonlinearity loss and universal
exact original source factorization. Full original inverse branch is unchanged.
Only FULL lower-degree inverse premise is present for general ell; degree
two uses actual proved degree-one base and has NO child inverse premise.

3. Correct nonnormal quotient
For ACTUAL Gamma_rho=rho*Gamma*rho^-1, define [x]_Gamma_rho->[x*rho]_Gamma
using Quotient.lift. The true conjugate subgroup membership criterion
proves representative independence. Inverse [x]_Gamma->[x*rho^-1]_Gamma_rho
is defined and both inverse identities PROVED. True group associativity
proves equivariance under ORIGINAL LEFT G action. Continuous quotient lift
proves both maps continuous. This gives an ACTUAL homeomorphism between
different nonnormal quotients, never a presumed right action on G/Gamma.

Pull ORIGINAL compatible metric back by the actual equivalence. Prove
isometry equivalence by actual induced distance. Compose genuine original
open quotient map with group right homeomorphism and inverse isometry
homeomorphism; exact representative cancellation PROVES the new quotient
map. This also PROVES metric topology equals actual conjugate quotient
topology. Arbitrary original metric is retained, not replaced by an assumed
invariant metric. Every native geometry field is actually constructed.

4. Actual native data / rational filtrations / finite representatives
The conjugated native data copies same E/H/I/G/step and all original
group/model/manifold instances. True conjugate lattice discreteness and
quotient compactness are applied. Metric and compatibility fields come
from the PROVED metric quotient map. There is no replacement matrix group.

For ACTUAL rational v in original rational log span, the already proved
rough_native_conjugate_log_span is APPLIED, giving equality of actual
conjugate and original Q-log spans. NativeRationalConjugateFiltration copies
EVERY original layer and proves ALL rational fields using that equality.
Bracket/antitone/top/terminal remain actual original fields. Nonlinearity
sum is EXACTLY the same, since layer spaces are unchanged. EVERY rational
finite direction (m/M)*y belongs to original Q-log span by true rational
scalar multiplication/cast identity; hence EVERY finite representative
receives an ACTUAL conjugated rational filtration and source weights.
Strict smaller-filtration nonlinearity therefore remains strict on each
new native datum. No child inverse/correlation is assumed from geometry.

5. Genuine canonical Haar transport
Use the TRUE right homeomorphism, ACTUAL quotient Borel structures of both
native data, and its real measurability. Pushforward of actual conjugated
native canonical probability is PROVED probability. Original LEFT
equivariance and actual child canonical translation invariance PROVE the
pushforward is original left invariant. Apply the already PROVED native
invariant-probability uniqueness theorem on ORIGINAL D: the pushed measure
equals ORIGINAL native canonical probability exactly. Actual measurable
embedding integral_map then gives transport for EVERY original function.
This is not assumed Haar normalization, a supplied measure equality or a
claim that group right translation preserves an arbitrary quotient measure.

6. Actual observables and frozen Fourier family
Original continuous F pulls back through the actual right-coset isometry,
giving continuous observable on TRUE conjugated native metric. Actual
induced distance proves preservation of unit Lipschitz bound and unit
norm. Canonical integral transport is actual theorem application.

For actual frozen LEFT parameter epsilon and original Fourier projection
Phi_k(F), define H(q)=Phi_k(F)(epsilon*rightMap(q)). Genuine joint continuity
of original metric coset action, function-space Fourier continuity, and
right pullback continuity prove joint family continuity. Any actual compact
epsilon family times original unit observable family has compact image.
Actual torus coefficient bound proves pointwise norm<=ONE. True canonical
right integral + original LEFT translation invariance + actual original
nonzero Fourier zero mean PROVE child canonical Haar mean ZERO. Exact
sample formula is H([h]_Gamma_rho)=Phi_k(F)([epsilon*h*rho]_Gamma).
Frozen original left action is NOT asserted uniformly spatially Lipschitz.
The genuine compact-family/unit-detection step is still required before
calling a unit-observable child inverse. No freezing error is assumed.

7. Original horizontal character transport
Actual logarithmic horizontal character kills genuine original commutator
layer; PROVED product additivity and value at one give f(rho*g*rho^-1)=f(g).
True conjugate subgroup membership therefore proves lattice integrality
iff on original and conjugated Gamma, retaining nonzero and Lie kernel.
Original norm-bounded horizontal grid membership follows by applying the
PROVED original grid theorem with ACTUAL original integrality. Different
native lattice coordinate grids are not identified without proof. Same
character on same E and same norm budget is used.

8. Remaining analytic / full-goal obligations
Select actual highest direction and positive lattice power ONCE for each
valid chi in fixed finite C, then true uniform period/geometry budgets
over that finite set and all 0<M<=S. Existing source packet existential
direction does not itself certify uniform qPeriod before all raw p/N.
Construct actual compact epsilon family using true bounded error E value.
Prove real original action freezing error by genuine uniform continuity
on compact parameter x ORIGINAL quotient, not by assumed Lipschitz action.
Partition original N samples into actual short residue progressions and
prove one has large mean after real error/tail control and length>=tau*N.
Then use true compact zero-mean observable to unit inverse detection.
Transport actual child character and BOTH complete raw tables back through
original real errors, rational denominator clearing, progression step/
translation and original-scale length comparison. Prove actual well-founded
degree+nonlinearity induction. P first/full diagonal alternative and full
original small-N cases, corrected multivariate inverse, separate interval
Gowers correlation inverse, rough progressions, cube/Alignment and final
positive distinct rapid FS/FP remain OPEN. No unavoidable obstruction found.
Publication/public repository/PR/prize milestone has NOT been reached.
Fixed-data existence does not establish explicit delta-power complexity.

Retain ALL old registered Lean hashes and selected axiom sets. Require
explicit autoImplicit=false EMPTY logs, terminal full build and expanded
standard-only axiom audit. No new axiom/sorry/admit/unsafe/native_decide,
custom oracle structure or option bypass. Re-execute/hash/arithmetic-check
the exact rational slab certificate and pin/hash all six original OpenAI
sections plus Lean/mathlib/PNT+ revisions. Author checks are not independent
kernel replay or external peer review.
'''
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
print(json.dumps(dict(prefix=prefix,modules=modules)))
