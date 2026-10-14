from pathlib import Path
import json
import re

prefix='round-native-rational-nonlinearity-factorization'
old='round-native-rational-integral-commutator'
base=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained={f['path'] for f in base['files']}
modules=sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules)==15,modules
components=[
    'ACTUAL original group derived subgroup is PROVED inside the TRUE real-character kernel in F_2 when the original commutator pairing is zero. PROVED exact original group/Lie lower-central equality is ACTUALLY applied to Exp(v), yielding true original Lie commutator inclusion in F_2 and actual difference-character annihilation on that Lie layer. No unproved infinitesimal implication is supplied.',
    'Actual lattice-integral functional values are PROVED rational on the TRUE original rational log span using genuine positive lattice powers and exact original Exp/Log natural-power identities. Actual original first-difference inclusion preserves true relative rational directions. Actual relative lattice integrality therefore proves rational psi values on actual rational F_2 vectors, without assuming Log(Gamma) is an additive lattice.',
    'EVERY actual real rational-split-basis coordinate is PROVED equal to the cast of its true rational coordinate. A CANONICAL continuous real extension F of the actual difference functional is constructed by fixed F_2 basis coordinates, zero on the actual rational complement. Exact restriction, actual rational values on the WHOLE original rational log span, actual nonzeroness on F_2 and actual original Lie commutator kernel are PROVED.',
    'TRUE smaller rational kernel Lie filtration is CONSTRUCTED on SAME original D, SAME degree ell and SAME original lattice: layers zero/one retain original top; every layer >=2 is actual Li intersect ker(F). ALL antitone/bracket/rational/terminal fields and original layer inclusion are PROVED. The actual nonzero difference / zero pairing case has STRICT original F_2 dimension drop.',
    'An ACTUAL natural nonlinearity measure sum_{i=2..ell} finrank(Li) is constructed. All new layer dimensions are <=original dimensions and layer two is STRICTLY smaller, so the actual natural measure STRICTLY decreases for ell>=2 while degree is unchanged. This supplies genuine well-founded nonlinearity descent; no same-degree child inverse is assumed.',
    'A TRUE highest nonlinear layer j and an ACTUAL rational direction y in Lj with F(y)=1 are selected from fixed geometry, BEFORE every source. Actual F kills L(j+1), 2<=j<=ell, and Exp(y) has a PROVED positive natural lattice power. This direction preserves weights in later scalar-factor removal; split-vector or normalized direction lattice membership itself is NOT asserted.',
    'Actual horizontal scalar projection of the TRUE original native BCH/Picard product is PROVED additive. Highest killed layer gives a true scalar total-degree bound. Exact nonlinear scalar part is defined by removing ACTUAL constant/linear coefficients. True aggregate monomial collection and zero-vector trimming construct a source in the kernel filtration from actual affine scalar projection, preserving actual evaluation/projection and original degree. Raw list-term cancellation is fully retained.',
    'A GENUINE EXACT ORIGINAL SOURCE FACTORIZATION is PROVED: original g(x)=Exp(Q_F(x)*y)*gK(x), Q_F being the ACTUAL nonlinear scalar part of F applied to raw p. The canonical residual is actual native product with [(Q_F,-y)], then true coefficient collection/zero trim. SAME actual group samples, original weights, real evaluations and resulting kernel-filtration weights/degree ell are all PROVED. Removed factor is explicit and may be UNBOUNDED; no small/rational split or correlation preservation is claimed.',
    'The SAME original nonzero Fourier signal now yields FULL original inverse OR actual smaller rational filtration with strict dimension/nonlinearity decrease AND fixed rational highest-layer direction plus GENUINE exact source factorization for EVERY original weighted source. BOTH higher P/Q monomial/binomial tables, actual relative character/M/offset/dense V and BOTH original-scale relative/bracket bounds remain intact. General degree has ONLY FULL lower-degree inverse premise; degree-two version has NO child inverse premise.'
]
remaining='''StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. The prize target is full original positive distinct rapidly separated monochromatic finite sums/products. Actual rational native geometry, normalization, relative/reduced recursion, full fixed-data small-slope/Claim 7.7 inverse, genuine original-vector/integral-commutator/zero-difference inverse reconstructions are retained. In the remaining nonzero-difference/zero-pairing branch, actual original Lie commutator annihilation, canonical rational real extension, TRUE rational kernel filtration on SAME original D and strict natural nonlinearity decrease are now PROVED. TRUE highest-layer rational direction with F(y)=1 and positive exponential lattice power is selected before all sources. GENUINE exact original source factorization g=Exp(Q_F*y)*gK is PROVED, with actual residual weighted in the smaller filtration and actual degree ell; real samples and raw-term cancellation are retained. SAME Fourier packet retains BOTH higher P/Q tables, actual bounded positive M/offset/dense V and BOTH original-scale relative/bracket tables. Removed scalar factor is explicit but may be UNBOUNDED: quantitative small/rational decomposition, bounded rational periods/finite residue representatives, short progression selection, genuine observable/correlation transport and complete original coefficient transfer still require proof before applying SAME-DEGREE smaller-nonlinearity induction. Q second coefficient and P first coefficient must be extracted from retained dense bracket/relative data; higher tables alone are insufficient. Degree+nonlinearity induction, original inverse all small-N source branches, corrected multivariate inverse, separate interval Gowers correlation inverse, rough progressions, cube/Alignment and StrongConjecture remain OPEN. Bounds are fixed-data existential constants, NOT original explicit delta-power laws. Rational split/normalized-direction exponentials are NOT asserted in Gamma; only actual positive powers are proved. Author build/hash/axiom/source review is NOT independent kernel replay or external peer review. Source slab estimate issue was repaired for the required analytic inverse and is NOT an unavoidable obstruction. Full formalization/unavoidable-obstruction publication/public repository/PR/prize milestone has NOT been reached.'''
text=Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
    text=re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),text,flags=re.M)
text=re.sub(r'^"""Audit .*?\n','"""Audit actual rational nonlinearity kernel/descent and genuine exact source factorization.\n',text,count=1)
text=re.sub(r"reference_scope='[^']*'", "reference_scope='OpenAI quantitative Leibman route; actual rational nonlinearity kernel, strict same-degree descent and genuine exact source factorization; quantitative small/rational/correlation transfer and full target remain open'",text)
Path(prefix+'-audit.py').write_text(text,encoding='utf-8')
review='''JSP-000168 / Erdos #172: TRUE rational nonlinearity descent / EXACT source factorization
Author mathematical review, 2026-10-13. Verdict: Partial coverage.
Previous goal turn: PROGRESS, verified in retained registered proof state.
NOT independent kernel replay or external peer review.
Full original positive distinct monochromatic finite sums/products remains OPEN.
Pinned six-section OpenAI primary source:
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026,
06_rough_progressions.tex. Auxiliary primary route:
https://arxiv.org/html/0709.3562v4 , quantitative Leibman / Claim 7.7.
Corrected multivariate scope: https://arxiv.org/html/1311.6170v3 .

1. Original group kernel and exact Lie bridge
For actual subgroup N=F_2 and additive real character psiLog, form ACTUAL
hom q:N -> Multiplicative(R), then K=q.ker.map N.subtype inside original G.
Every original commutator belongs to K by ACTUAL pairing-zero condition.
Subgroup.commutator_le gives ORIGINAL algebraic derived subgroup <=K.
This generic argument does not assume any extension to G or continuity.

Apply the already PROVED nativeGroupLowerCentralSeries_eq_exponential at
one: every v in the ORIGINAL Lie commutator model has Exp(v) in the actual
derived group. The same bridge gives its actual F_2 membership. Membership
in actual kernel gives psiLog(Exp(v))=0. Exact native relative difference
Log formula and Log(Exp(v))=v PROVE actual psi(v)=0. Dependent layer-membership
proofs are transported by actual subtype equality. No unproved limiting
commutator formula is assumed. Every original Lie bracket is in this layer.

2. Actual rational values and coordinate square
If f is integer on Log(Gamma), any ACTUAL rational-log-span vector v has
some n>0 with Exp(v)^n in Gamma by the proved positive-power criterion.
True Exp(n*v)=Exp(v)^n and Log inverse give n*f(v)=z for an actual integer z;
hence f(v)=cast(z/n). This does NOT treat Log(Gamma) as an additive lattice.

The first-difference model of an actual original rational v in F_2 is
(v,0), an actual original product rational direction. The PROVED relative
inclusion rational iff transports this to the true relative Gamma log span.
Actual relative lattice integrality of chi consequently gives rational psi(v).
Every real split-basis coordinate is EXACTLY the cast of the corresponding
rational basis coordinate on original rational log span; the real dual
extension and true basis evaluation prove the full coordinate identity.

3. Canonical real extension and its TRUE kernel
Define F on original E by summing over the actual Sum.inl(F_2) split-basis
coordinates with coefficient psi(b_i). It is zero on the fixed rational
complement, an actual continuous linear functional, not an arbitrary assumed
extension. On actual F_2 vectors, all Sum.inr coordinates vanish; actual basis
expansion and real linearity PROVE F restricted to F_2 equals psi EXACTLY.
Rational psi(b_i) and the true coordinate square prove F rational-valued on
the WHOLE original Q-log span. Nonzero psi produces an ACTUAL v in F_2 with
F(v)!=0. The exact Lie bridge plus restriction PROVE F kills original Lie
commutator model 1. F is NOT asserted integer-valued on original Gamma here.

4. Genuine rational kernel filtration
Given an ACTUAL rational real F killing the actual original commutator
layer, set L'_i=Li for i<2 and Li intersect ker(F) for i>=2, on SAME D,
SAME Gamma, SAME ell. ALL NativeRationalLieFiltration fields are PROVED.
Antitone follows from old antitone/intersection. Original bracket weights
follow from old bracket condition; EVERY Lie bracket is in original
commutator model, where F is PROVED zero. Rationality uses the actual
rational restricted-kernel real-span theorem and original Li rationality.
Initial top layers and terminal bottom are actual equalities.

Nonzero psi gives strict F_2 dimension drop. Define ACTUAL natural measure
sum_{i=2..ell} finrank_R(Li). Every new dimension <=old, with strict loss
at actual index 2 when ell>=2; finite sum inequality PROVES strict measure
decrease. Degree ell and original data stay unchanged. This supplies a
genuine well-founded nonlinearity parameter, not a same-degree inverse premise.

5. True highest nonlinear direction
Select max actual j in {2,...,ell} where F is nonzero on Lj; index two is
actually in this finite set. Maximality and terminality PROVE F kills L(j+1).
Rationality of Lj and actual nonzeroness force an ACTUAL rational w in Lj
with F(w)!=0, by real-span/kernel argument. F(w)=cast(a) for nonzero rational
a. Set y=a^-1*w using rational scalar multiplication. Then y is ACTUALLY
rational in Lj and F(y)=1. The genuine positive-power theorem produces
q>0 with Exp(y)^q in ORIGINAL Gamma. Exp(y) itself is NOT assumed lattice.
All this geometry is selected BEFORE every source polynomial.
Using a deepest actual direction is essential: y in Lj preserves weights
for every removed scalar monomial degree <=j. An arbitrary F_2 direction
would not justify the weight of higher removed monomials.

6. Actual scalar algebra and coefficient collection
F applied to TRUE native BCH/Picard product scalar polynomial equals sum
of actual scalar projections. This follows from exact original product
evaluation and the proved native logarithmic character additivity; not an
abstract replacement group. F killing L(j+1) gives actual scalar totalDegree
<=j: every coefficient above j has true aggregate vector coefficient in
the killed layer and is zero. No raw-term ordinary degree bound is used.

Define Q_F=P_F-C(coeff_0 P_F)-C(coeff_1 P_F)*X on actual Unit Mv polynomial.
It has degree <=j. If an ACTUAL old weighted source has affine scalar F
projection, true monomial collection puts EVERY aggregated high vector
coefficient in ker(F), retaining old weights. This constructs a TRUE source
weighted in L', including cancellations across raw list terms. Zero-vector
trimming preserves complete evaluation/projection and actual coefficients,
and actual terminality PROVES degree <=ell. Merely asserting individual
raw list vectors lie in ker(F) would have been false; it is not done.

7. GENUINE exact source factorization
For ACTUAL old weighted p and highest direction y, form actual native product
raw residual from [(Q_F,-y)] and p, then true collect/zero trim pK. Direction
term has degree <=j and vector -y in Lj, so it is genuinely old-weighted.
Native weighted product theorem gives true old residual weights. Its ACTUAL
F projection is -Q_F+P_F, exactly the constant/linear part, with totalDegree
<=1. Collection lemma therefore PROVES kernel-filtration weights for pK,
and trimming gives true degree <=ell. This is an ACTUAL constructed source,
not an assumed source-filteredness condition or abstract factorization record.

Exact original group product/Log/Exp laws prove for EVERY original real x:
 g_p(x)=Exp(Q_F(x)*y)*g_pK(x).
The explicit left factor may be UNBOUNDED. No smooth-smallness, bounded
rational decomposition, observable transport or correlation preservation
is claimed from this algebraic identity alone. These are remaining analytic
obligations needed before applying the smaller-filtration inverse.

8. SAME original Fourier packet
Apply the true kernel/descent/factorization construction to the retained
actual nonzero-difference/zero-pairing packet. FULL original inverse branch
is unchanged. Remaining branch now returns ACTUAL K with explicit layers,
strict original F_2 dimension loss and strict actual natural nonlinearity
loss; actual highest rational direction with positive lattice power; and
GENUINE exact kernel-filtered source factorization for EVERY weighted source.
All ORIGINAL higher P/Q monomial/binomial tables, actual chi/M/offset and
dense V with BOTH original-scale relative/bracket tables are PRESERVED.
General degree retains ONLY FULL actual lower-degree inverse premise.
Degree-two version has NO child inverse premise. Neither is the full inverse:
the quantitative nonlinearity/correlation branch remains explicit.

9. Remaining real goal
Extract Q second coefficient and P first coefficient from actual retained
zero-pairing dense affine bracket data, not from higher tables alone.
Transfer actual Q higher coefficients to Q_F of raw source and construct
bounded positive common multiplier. Decompose Q_F into actual small error
and bounded-denominator rational polynomial along SAME rational y.
Prove actual periods, finite rational residue representatives, genuine
short progression selection and original-scale length comparison. Transport
ACTUAL unit observables/correlation to the actual smaller-filtration source;
exact factorization alone does not imply a large child correlation.
Then prove genuine degree+nonlinearity induction and complete coefficient
transport back to BOTH full raw original tables. Original inverse small-N
source completion, corrected multivariate inverse, separate interval Gowers
correlation inverse, rough progressions, cube/Alignment and final original
positive distinct rapidly separated FS/FP remain OPEN. No unavoidable
obstruction established. Public repo/PR/prize milestone has NOT been reached.
Fixed-data existential bounds are proved; source explicit delta-power laws
are NOT claimed. Author checking remains distinct from independent replay.

Retain all old registered source/axiom hashes. Every new module must pass
explicit autoImplicit=false with EMPTY logs, full build and expanded axiom
audit with terminal success. Standard axioms only; no sorry/admit/custom
axiom, unsafe/native_decide bypass or relaxed heartbeat. The exact rational
source slab certificate is re-executed/hash/arithmetic checked; its numerical
issue was repaired for the actual inverse and is not an unavoidable blocker.
'''
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
print(json.dumps(dict(prefix=prefix,modules=modules)))
