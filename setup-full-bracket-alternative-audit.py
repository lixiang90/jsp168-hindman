from pathlib import Path
import json
import re

prefix = 'round-native-rational-full-bracket-alternative'
old = 'round-native-rational-zero-slope-bracket'
base = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained = {f['path'] for f in base['files']}
modules = sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules) == 14, modules
components = [
    'TRUE affine-basepoint torus inverse is PROVED on SAME range samples. Actual Fourier point addition and norm ONE cancel the basepoint phase exactly. Genuine compact Fourier selection yields an ACTUALLY NONZERO integer vector with fixed size and original length^-1 phase bound, before all unbounded frequencies/basepoints.',
    'Actual dense affine small values PLUS the initial N^-1 ABSOLUTE slope bound force N*abs(alpha)<=C*w for large enough N. Both the small-tolerance nearest-integer branch and large-tolerance branch are proved; the bounded natural q has abs(q*alpha)<=1/2 before circle norm is replaced by absolute value. No false implication from circle-small to real-small is used.',
    'TRUE complete dense interval block selection is PROVED: L=N/J, actual leftover has cardinality <=J, 2J<=delta*N leaves actual density delta/2, actual division labels and modulo injection select one complete original block. Actual block endpoint is <=N; short-block density is NOT assumed.',
    'Actual small-slope bracket samples yield affine small values and relative slope refinement. SAME original shifted samples a+n are used in the true affine slab cutoff/discrepancy/inverse. Freezing costs <=C*w/J; genuine original-scale error B/N and fixed J make the tolerance <=c*w. Original N/L<=2J transports the actual vector phase bound back to ORIGINAL N.',
    'FULL SMALL-LINEAR-SLOPE fractional bracket inverse is PROVED for ANY finite index type, including empty and zero coefficient cases, all positive N and small-N alternatives. All fixed-data budgets precede EVERY beta/alpha/zeta/gamma/N. Output is actual REAL coefficient bounds at original N^-1 scale OR an ACTUALLY NONZERO bounded original integer vector with small k dot gamma. No bracket oracle or unsupported explicit delta power law.',
    'FULL fixed-data Claim 7.7 bracket alternative is PROVED by ACTUALLY applying the small-slope inverse SECOND time to the true nearest-integer correction. Mixed r=0, positive/negative r, actual filter inclusion and positive natAbs multiplier are discharged. Output is one truly positive bounded natural r making every original r*zeta circle-small OR a nonzero original integer vector with small k dot gamma ALONE.',
    'The FULL bracket alternative is APPLIED to SAME actual native compact parameters/useful shifts and original Fourier signal, preserving true relative character/grid/norm, bounded positive NATURAL M, actual bounded integer offset and BOTH higher P/Q monomial/binomial tables. General degree retains ONLY FULL actual lower-degree child inverse; degree-two has NO child inverse premise.',
    'The actual nonzero first-layer-vector branch is NOW COMPOSED with the fully proved original character reconstruction: original nonzero horizontal/lattice character, original finite grid/operator bound, BOTH COMPLETE raw monomial and Mv-binomial tables for EVERY positive Unit multiindex. The exact remaining alternative preserves the actual relative character/M/higher P/Q/offset packet and positive multiplier controlling all actual commutator coefficients. All original/relative budgets precede source inputs; degree-two discharge has NO child inverse premise.'
]
remaining = '''StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Full original positive distinct rapidly separated monochromatic finite sums/products remains the prize target. Retained proofs cover true rational native filtration, original compact normalization, genuine relative/reduced geometry/degree/rational lattices and original coefficient reconstruction. The corrected torus slab geometry, FULL small-linear-slope bracket inverse and FULL fixed-data Claim 7.7 alternative are PROVED, including actual small-N cases of this ANALYTIC lemma, arbitrary finite indices, positive natural multipliers and original N scale. They are applied to the SAME actual Fourier signal and BOTH higher P/Q tables. Original small nonzero k dot gamma branch is fully discharged with BOTH COMPLETE original raw monomial/Mv-binomial tables. This is NOT the full original inverse: remaining case (i) requires true commutator character lattice integrality/rational denominators, common multiplier absorption, actual reducible rational nonlinearity filtration/factorization and genuine degree+nonlinearity induction. Split-basis exponentials are NOT asserted to lie in Gamma; coordinate image is only proved contained in Z^m. General native signal still has only full lower-degree inverse premise; degree-two bracket/discharge has none. Original inverse small-N source branches, corrected multivariate inverse, separate interval Gowers correlation inverse, rough progressions, cube/Alignment and StrongConjecture remain OPEN. Bounds proved here are fixed-data existential constants, NOT the original explicit delta-power dependence. Source Proposition 5.3 displayed slab estimate has an exact rational counterexample, but the proposition's needed qualitative quantitative alternative is repaired formally; this is NOT an unavoidable obstruction. Author build/hash/axiom/source review is NOT independent kernel replay or external peer review. Publication/public repository/PR/prize application milestone (full formalization or genuine unavoidable obstruction) has NOT been reached.'''
text = Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
    text = re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),text,flags=re.M)
text = re.sub(r'^"""Audit .*?\n','"""Audit full small-slope/Claim 7.7 inverse and actual native original-vector discharge.\n',text,count=1)
text = re.sub(r"reference_scope='[^']*'", "reference_scope='OpenAI quantitative Leibman route; corrected full fixed-data Green-Tao Proposition 5.3 and Claim 7.7; native Fourier application and original-vector discharge; case-(i) nonlinearity/full target remain open'",text)
# The certificate generator intentionally writes its historical fixed filename.
text = text.replace("Path(OLD+'-slab-review.json').read_bytes()", "Path('round-native-rational-fractional-bracket-input-slab-review.json').read_bytes()")
# After a prepare failure, reuse only terminal explicit checks whose exact
# command, source and EMPTY log hashes are unchanged. Full build is still run.
needle = '''    results = []
    for p in MODULES:
        result = run'''
replacement = '''    results = []
    saved = obj(PREFIX+'-focused-results.json') if Path(PREFIX+'-focused-results.json').exists() else []
    for p in MODULES:
        prior = next((r for r in saved if r['module']==p), None)
        if (prior and prior['terminal'] and prior['exit_code']==0
            and prior['command']==['lake','env','lean','-DautoImplicit=false',p]
            and prior['source_sha256']==digest(p)
            and prior['log_sha256']==digest(prior['log']) and not read(prior['log']).strip()):
            results.append(prior)
            print('Retained exact explicit check '+p, flush=True)
            continue
        result = run'''
assert text.count(needle)==1
text = text.replace(needle,replacement)
Path(prefix+'-audit.py').write_text(text,encoding='utf-8')
review = '''JSP-000168 / Erdos #172: FULL fixed-data bracket alternative / original-vector discharge
Author mathematical review, 2026-10-13. Verdict: Partial coverage.
Previous goal turn: PROGRESS. NOT independent replay or external peer review.
Full positive distinct monochromatic finite-sums/products target remains OPEN.
Primary pinned source: https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026,
06_rough_progressions.tex. Auxiliary primary source:
https://arxiv.org/html/0709.3562v4 , Proposition 5.3 / Claim 7.7.
Corrected multivariate scope: https://arxiv.org/html/1311.6170v3 .

1. Exact affine inverse
Actual torus Fourier addition is proved on POINTS, not confused with
frequency addition. Actual Fourier basepoint phase has complex norm ONE.
Factoring it from the actual finite mean preserves its norm exactly.
Compact unit-observable selection produces a genuinely nonzero frequency.
The actual geometric mean inverse then gives length^-1 scale. One fixed
natural size/error budget precedes ALL frequencies, basepoints and lengths.
This uses SAME circle Haar and does not assume a shifted-interval inverse.

2. Relative affine slope
Let epsilon=B/N+D*w with w>=0 and B<=N*w. Choose T before alpha,beta,w,N,
including 2*A*A0 and 20*B/delta, where A is the proved affine inverse bound.
If epsilon<=delta/10, actual affine recurrence produces 1<=q<=A and
N*norm(q*alpha)<=A*epsilon. Initial N*abs(alpha)<=A0 and N>=2*A*A0 imply
abs(q*alpha)<=1/2, so its circle norm is its actual absolute value. Since
q>=1, N*abs(alpha)<=A*(D+1)*w. No wrap-around is ignored.
If epsilon>delta/10, B/N<=delta/20 forces delta<=20*D*w. The INITIAL
absolute slope bound gives N*abs(alpha)<=20*D*A0*w/delta directly.
The fixed C covers both branches. D=0/w=0 edge cases are included.

3. Actual dense complete block
Set L=N/J. Original useful points beyond J*L form a true subset of
Ico(J*L,N), with card<=J, by the actual division-remainder identity.
If 2J<=delta*N, the retained useful set has card>=delta*N/2.
Actual labels floor(n/L) lie in range J. Proved finite dense witness
selection gives one label with V.card*J>=retained.card. On that fiber,
n mod L is injective and j*L+(n mod L)=n, proving actual block density
delta*L/2. The block endpoint (j+1)*L<=N is actually proved.
The remainder and a useful block are NEVER assumed dense without proof.

4. Same shifted samples and freezing
Actual fractional bracket bounds imply affine beta+alpha*h circle bounds
at tolerance B/N+D*w, because fract(h*gamma_i) lies in [0,1).
After relative slope refinement N*abs(alpha)<=C*w, actual n<L=N/J gives
abs(alpha*n)<=C*w/J. Freezing beta+alpha*a retains fract((a+n)*gamma_i)
on the SAME original useful points. Circle triangle inequality bounds
the frozen expression by B/N+C*w/J.
The affine torus basepoint is exactly a*gamma modulo one; no fractional
representative translation identity is assumed. True slab membership,
unit cutoff discrepancy and the actual affine inverse apply on range L.

5. Full small-slope inverse budgets and branches
Select maximal nonzero zeta_none, w=abs(zeta_none). The corrected full
torus slab argument gives fixed c and K before all raw source inputs,
now at density delta/2. Choose J=ceil(4*C/c)+1 and threshold T including
J and ceil(2J/delta), before raw inputs. If N<T, N*abs(zeta_i)<=T*Z.
If N*w<=P=B+4*B/c, all real coefficient bounds follow directly.
Otherwise B<=N*w, refinement/block selection apply; B/N<=c*w/4 and
C*w/J<=c*w/4, so actual frozen tolerance<=c*w. Actual affine inverse
produces nonzero k with L*norm(k dot gamma)<=K. The previously proved
N/L<=2J yields ORIGINAL N*norm(k dot gamma)<=2J*K. The final fixed
natural A absorbs small-N, small-w, phase and size budgets.
Arbitrary finite indices are handled by actual maximal coordinate
reindexing; finite simultaneous budgets precede selection. Actual
nonzeroness, natAbs sum and dot-product equality transport exactly.
Empty index types/zero coefficients give the real-coefficient branch.
Thus the FULL small-linear-slope lemma is proved, without an analytic oracle.

6. Full fixed-data Claim 7.7
First apply the already proved unrestricted-alpha mixed alternative.
Its coefficient-small branch uses r=1. A mixed pair (k,r) with r=0
already gives a nonzero original k dot gamma. For r!=0 set
a=r*alpha+k dot gamma, alpha'=a-round(a), zeta'=r*zeta-k,
beta'=r*beta. The proved correction gives N*abs(alpha')<=Q,
abs(zeta'_i)<=Q*(Z+1), and SAME original useful set satisfies corrected
circle bound Q*B. Filter inclusion transports density with NO loss.
Apply the newly proved small-slope inverse SECOND time, with these fixed
budgets. Its nonzero-vector branch gives original k dot gamma ALONE.
Its real-coefficient branch bounds circle norms of r*zeta_i by their
actual distance to integer k_i. Replacing r by its positive natAbs
preserves circle norms for either sign. Thus the full positive bounded
natural multiplier OR nonzero original integer-vector alternative is proved.
All constants precede ALL beta/alpha/zeta/gamma/N. Original explicit
delta-power dependence is NOT claimed; fixed-data existential bounds suffice
for this milestone, not a complete complexity audit of the source theorem.

7. True native application and original-vector discharge
Apply full Claim 7.7 to actual compact native bracket parameters and SAME
useful V subset range N, with density capped at min(rho,1). Actual character,
positive bounded M, BOTH higher P/Q monomial/binomial tables and bounded
integer offsets are retained. The child inverse premise is only the FULL
actual lower-degree statement; degree-two versions discharge it using the
proved degree-one base. They are NOT the full original degree-two inverse.

The pure-vector output gives v!=0, sum natAbs(v_i)<=A and original-scale
small v dot gamma. Each abs(v_i)<=A is proved via a finite sum inequality.
Apply the existing original reconstruction with fixed R=B=A BEFORE sources.
This gives a true nonzero horizontal/lattice character on the ORIGINAL
group, bounded norm and finite grid, and BOTH COMPLETE original raw
monomial/Mv-binomial tables for EVERY positive Unit multiindex.
The OR theorem now leaves only the actual relative commutator-coefficient
packet with positive multiplier; it does NOT hide that branch as a proof
of the original inverse. No new named statement or inverse oracle is added.

8. Scope and next obligations
Actual case (i) still needs common multiplier absorption, rational
denominators and lattice-integral commutator characters. Split-basis
exponentials are NOT assumed lattice points. The zero-character case
needs actual smaller rational nonlinearity filtration AND genuine source
factorization, followed by degree+nonlinearity induction. Original inverse
small-N completion, corrected multivariate inverse, separate interval
Gowers correlation inverse, rough progressions, Alignment and StrongConjecture
remain OPEN. The full target has not been proved and no unavoidable
obstruction has been found. Public repository/PR/prize milestone not reached.

All retained registered proof-source hashes/axiom sets must remain unchanged.
Explicit autoImplicit=false checks require EMPTY logs for every new module,
full build and expanded axiom audit require terminal success. Only
propext/Classical.choice/Quot.sound permitted; no sorry/admit/custom axioms,
unsafe/native_decide bypass or relaxed heartbeat configuration.
The exact rational reviewed source-slab certificate is re-executed and
hashed; it refutes the displayed volume estimate, not Proposition 5.3 itself.
The corrected full torus estimates and needed inverse are now PROVED in Lean.
'''
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
print(json.dumps(dict(prefix=prefix,modules=modules)))
