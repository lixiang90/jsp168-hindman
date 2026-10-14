from pathlib import Path
import json
import re

prefix = 'round-native-rational-integral-commutator'
old = 'round-native-rational-full-bracket-alternative'
base = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained = {f['path'] for f in base['files']}
modules = sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules)==11,modules
components = [
    'ACTUAL original commutator pairing is PROVED antisymmetric; first-variable continuity and TRUE F_2 kernel follow. Genuine original Lie real linearization constructs actual continuous linear characters in the first variable, with exact original logarithm evaluation and actual layer-2 kernel. No original lattice character is assumed.',
    'A TRUE GEOMETRY-ONLY rational split-basis matrix in the actual original smooth lattice basis and ONE positive common natural denominator are constructed. Actual real scalar expansion is PROVED for every original real functional, and denominator-cleared integrality follows from integer values on actual smooth lattice basis vectors. Exponentials of rational split-basis vectors are NEVER asserted lattice points.',
    'TRUE ORIGINAL lattice-integral commutator characters tau_i=d*B_chi(-,Exp(b_i)) are constructed. Original lattice integrality is PROVED using genuine right-variable real linearization, actual lattice commutator integrality, actual Exp(e_j) lattice membership and the fixed rational matrix denominator. They kill TRUE F_2; each actually NONZERO tau_i is a genuine ORIGINAL horizontal/lattice character.',
    'A genuine finite-relative-grid candidate operator-norm budget is PROVED before every raw polynomial/length and selected relative character. Invalid relative functionals contribute zero in the auxiliary finite sum; for every valid witness the exact actual character is retained by proof irrelevance. No norm/inverse oracle is introduced.',
    'BOTH COMPLETE original raw monomial/Mv-binomial coefficient tables are PROVED for ANY true lattice character killing F_2, from its actual compact first evaluation. Actual two-normalization integer transport, all positive Unit multiindices and high-degree zero terms are discharged; the theorem is not restricted to named first-layer integer characters.',
    'A positive bounded natural multiple of an ACTUAL NONZERO integral commutator candidate now gives the FULL ORIGINAL inverse conclusion. Exact compact evaluation is (q*d) times the actual scaled bracket coefficient; positive geometry-only integer multiplication transports circle error at SAME original N scale. True original horizontality/nonzeroness/grid/norm and BOTH COMPLETE raw coefficient tables are PROVED with ONE fixed natural budget before all sources.',
    'When EVERY actual candidate tau_i vanishes, the ACTUAL commutator pairing is PROVED zero on EVERY pair of original group points. The positive geometry denominator is canceled only after actual character evaluation; true first-layer factorization gives every coefficient zero. Empty index types are included. This does NOT yet assert a smaller source filtration or Lie differential annihilation.',
    'The actual ZERO difference-character branch is FULLY reconstructed from one ACTUAL useful shift. Original diagonal character is genuinely nonzero/horizontal/lattice bounded; BOTH COMPLETE raw coefficient tables include EVERY positive multiindex. Above the true degree, exact zero-vector trimming preserves raw projection and proves coefficients vanish. No false raw termwise degree bound is asserted.',
    'The SAME actual nonzero Fourier signal now yields FULL original inverse OR a NONZERO actual F_2 difference character whose commutator pairing vanishes on ALL original points. BOTH higher P/Q monomial/binomial tables, SAME bounded positive M, actual integer offset, true dense V and BOTH original-scale relative coefficient tables/bracket bounds on V are PRESERVED. Nonzero original-vector, nonzero candidate and zero-difference branches are discharged. General degree retains ONLY FULL actual lower-degree child inverse; degree-two version has NO child inverse premise.'
]
remaining = '''StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Original positive distinct rapidly separated monochromatic finite sums/products is the prize target. Actual rational native geometry, normalization, relative/reduced recursion, corrected torus slab estimates, FULL fixed-data small-slope/Claim 7.7 alternative and original-vector reconstruction are retained. TRUE original commutator characters with GEOMETRY-ONLY rational matrix denominator and actual lattice integrality are now PROVED; nonzero candidate yields BOTH COMPLETE raw original coefficient tables and original nonzero horizontal/grid/norm conclusion. Zero difference-character also gives FULL original reconstruction from one actual useful relative sample. SAME original Fourier signal therefore reduces to full original inverse OR a NONZERO actual F_2 difference character with pairing zero on EVERY original g,h, retaining BOTH higher P/Q tables, actual positive bounded M/offset/dense V and BOTH original-scale relative tables/bracket bounds on V. Remaining rational nonlinearity branch requires actual Lie-differential annihilation/rational kernel, TRUE smaller filtration with strict nonlinearity dimension drop AND genuine source factorization/correlation transport; group pairing zero is NOT silently promoted to an already proved Lie-kernel filtration. Degree+nonlinearity induction, original inverse small-N completion, corrected multivariate inverse, separate interval Gowers correlation inverse, rough progressions, cube/Alignment and StrongConjecture remain OPEN. Bounds are fixed-data existential constants, NOT original explicit delta-power laws. Split-basis exponentials are NOT asserted in Gamma and coordinate image is NOT asserted all Z^m. The displayed source slab estimate was numerically false but its required qualitative quantitative inverse was repaired formally; not an unavoidable obstruction. Author build/hash/axiom/source review is NOT independent kernel replay or external peer review. Full-formalization/unavoidable-obstruction publication/public-repository/PR/prize milestone has NOT been reached.'''
text = Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
    text = re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),text,flags=re.M)
text = re.sub(r'^"""Audit .*?\n','"""Audit genuine integral commutator reconstruction and exact nonlinearity alternative.\n',text,count=1)
text = re.sub(r"reference_scope='[^']*'", "reference_scope='OpenAI quantitative Leibman route; actual Claim 7.7 commutator lattice-integrality/nonzero and zero-difference reconstruction; true nonzero-difference zero-pairing packet; smaller rational nonlinearity/factorization/full target remain open'",text)
Path(prefix+'-audit.py').write_text(text,encoding='utf-8')
review = '''JSP-000168 / Erdos #172: actual integral commutator and nonlinearity alternative
Author mathematical review, 2026-10-13. Verdict: Partial coverage.
Previous goal turn: PROGRESS, verified in retained registered proof state.
NOT independent kernel replay or external peer review.
Full positive distinct monochromatic finite-sums/products target remains OPEN.
Pinned OpenAI six-section primary source:
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026,
06_rough_progressions.tex. Auxiliary primary route:
https://arxiv.org/html/0709.3562v4 , Claim 7.7 / quantitative Leibman proof.
Corrected multivariate scope: https://arxiv.org/html/1311.6170v3 .

1. Actual left-variable linearization
For convention [g,h]=g*h*g^-1*h^-1, the actual subgroup commutator element
of (g,h) equals the inverse element of (h,g). Actual F_2 real difference
character is additive, so its value is antisymmetric. This PROVES left
continuity and the TRUE left F_2 kernel from the established right versions.
Actual additivity in first variable and continuity allow the proved native
real Lie linearization, producing a genuine continuous linear functional
with exact original Log evaluation. Exponentiating actual layer-2 vectors
proves the actual Lie layer-2 kernel. No lattice integrality is yet inferred
at this stage and no named inverse is assumed.

2. Geometry-only rational matrix denominator
The split basis b_i is RATIONAL in Log(Gamma) span. The actual ORIGINAL
smooth lattice basis e_j has an actual rational companion basis; its
real and rational coordinate maps commute. Matrix t_ij is this rational
companion coordinate of b_i. Finite rational denominator construction gives
ONE d>0, fixed only by D/L, with d*t_ij integral for all i,j.
Actual real basis expansion then proves, for EVERY real linear f,
 f(b_i)=sum_j cast(t_ij)*f(e_j).
If f(e_j)=z_j are integers, multiplying by d gives the actual integer
sum_j a_ij*z_j. Empty dimensions/index types are included.
Neither b_i nor Exp(b_i) is assumed lattice; only Exp(e_j) is a true lattice
point, by the established smooth basis theorem. This distinction is essential.

3. Genuine original integral candidate
Define tau_i=d*(actual left linearization at Exp(b_i)). Its original Log
evaluation equals d*B_chi(g,Exp(b_i)), EXACTLY. It kills original F_2.
For g in original Gamma, actually linearize the right character B_chi(g,-).
Each Exp(e_j) is in original Gamma, so the original lattice commutator
integrality theorem yields integer real-linearized values on every e_j.
Apply the actual scalar denominator theorem to b_i. This PROVES tau_i
is integer-valued on EVERY original lattice point, with the SAME d for
all chi/g/i. Every ACTUALLY NONZERO tau_i is consequently an ORIGINAL
nonzero horizontal/lattice character. Relative horizontality and its lattice
integrality are actual inputs already supplied by the native Fourier packet.

4. Fixed finite-family norm budget
The relative grid C is fixed BEFORE all source p/N. For each chi, define
the auxiliary candidate tau_i when the actual relative commutator-kernel
predicate holds, and zero otherwise. Sum their finitely many operator
norms over C and i. Actual finite-sum inequalities bound every valid
candidate's norm by this fixed nonnegative R. Proof irrelevance ensures
the exact same constructed candidate for EVERY actual kernel witness.
This is a proved finite norm bound, not an assumed analytic estimate,
and does not make constants depend on the subsequently selected p/chi/N.

5. General complete raw coefficient reconstruction
For ANY actual original lattice-integral real character f killing F_2,
the compact scalar source is affine. Its compact first coefficient equals
f(Log(a)) for actual a=compact source at one. True two-normalization
formula transports RAW first coefficient modulo an ACTUAL integer.
Higher raw scalar coefficients vanish by the actual weighted filtration,
not by an unsupported termwise raw degree assertion. Thus original N times
circle norm of f(Log(a)) controls EVERY positive Unit multiindex monomial.
The true finite Stirling/binomial conversion, including indices beyond the
declared degree box, gives BOTH COMPLETE Mv-binomial coefficients. Constants
retain the actual mvBinomialCoefficientBudget Unit ell factor.

6. Actual nonzero commutator inverse branch
For actual positive natural M and tau_i, f=M*tau_i is still a NONZERO
original horizontal/lattice character. Exact compact evaluation is
 (q*d)*nativeCompactBracketCoefficient(p,chi,M,i),
where q is the established positive first-layer coordinate denominator.
The factor q*d is a NATURAL integer fixed by D/L, so the proved natural
multiplier circle-norm bound transports the actual small bracket coefficient
at ORIGINAL N scale. Candidate norm is <=S*R for M<=S. One positive natural
Q absorbs S*R, (q*d)*B and BOTH full coefficient budgets, BEFORE p/N/chi/M.
Actual original finite grid membership follows from proved horizontal and
operator norm bounds. This gives the FULL ORIGINAL inverse CONCLUSION for
this branch; it is not the full original inverse THEOREM over all branches.

7. Actual zero-candidate and zero-difference branches
If every tau_i linear map is zero, evaluate each on Log(g), then cancel
the actual nonzero d to prove B_chi(g,Exp(b_i))=0. The TRUE first-layer
factorization therefore proves B_chi(g,h)=0 for EVERY original g,h.
No Lie differential/kernel or smaller source filtration is inferred yet.

When the actual F_2 difference character itself equals zero, an ACTUAL
relative useful shift gives exact diagonal scalar projection and original
coefficient transport. Actual relative nonzeroness plus zero difference
forces diagonal nonzeroness. Its norm is controlled by the already proved
geometry operator budget. Positive multiindices <=ell follow from the
actual relative tables. Above ell, zero-vector trimming preserves the
COMPLETE raw scalar polynomial and proves total degree <=ell, so actual
coefficients vanish. True binomial conversion covers all positive indices.
One fixed natural budget gives the FULL ORIGINAL inverse in this branch.

8. SAME actual Fourier signal / exact remaining packet
Start from SAME genuine dense fractional paper-separation packet, preserving
actual finite relative grid, positive M, BOTH higher P/Q tables, integer
offset b and nonempty dense V with BOTH original-scale relative coefficient
tables AND actual bracket bounds on V. Apply the proved full fixed-data
Claim 7.7 to SAME V using density min(rho,1), without replacing original N.

Pure integer-vector branch uses previous complete original reconstruction.
In coefficient-small branch, r>0 is genuinely bounded by fixed R. If some
actual tau_i is nonzero, M'=r*M is positive and <=R*S; its actual bracket
coefficient equals r times original M coefficient. Apply the new complete
commutator reconstruction at that SAME original scale. The higher P/Q
tables are unnecessary after the full original conclusion is obtained.

If all candidates vanish and the actual difference character is zero,
select one ACTUAL h in V and apply the complete pure-diagonal reconstruction.
Otherwise return the ACTUAL NONZERO difference character, ALL candidate
linear maps zero and pair B identically zero on EVERY original g,h.
SAME original M and BOTH higher P/Q tables are preserved, together with
actual offset and ORIGINAL dense V, ALL relative tables/bracket errors.
Uniform enlargement of scalar/norm/offset bounds precedes raw sources.
This explicitly restores data needed for the nonlinearity branch rather
than retaining only the higher coefficient tables. No first coefficient
bound is recovered from a high-order table without evidence.

General degree has ONLY the full actual lower-degree child inverse premise.
Degree-two version discharges this via proved degree-one base, with NO
child inverse premise. It is STILL not the full original degree-two inverse:
the NONZERO difference / zero-pairing nonlinearity branch remains explicit.

9. Remaining exact proof obligations
Prove actual Lie differential annihilation of the nonzero F_2 difference
character from the proved group pairing-zero condition. Prove actual
rational kernel, smaller filtration and strict nonlinearity dimension drop.
Then construct GENUINE source factorization/correlation preservation in that
filtration using retained P/Q and relative sample tables. Do NOT assert the
raw source automatically lies in Li intersect ker(psi). Genuine degree+
nonlinearity induction is still required. Full original inverse, original
small-N source completion, corrected multivariate inverse, separate interval
Gowers correlation inverse, rough progressions, cube/Alignment and final
positive distinct rapidly separated FS/FP remain OPEN. No unavoidable
obstruction has been established. Public repo/PR/prize milestone not reached.
Fixed-data existential bounds are proved; explicit delta-power laws remain
distinct and are NOT claimed. The source numerical slab issue is repaired
for the actual required inverse and is not an unavoidable blocker.

Every retained registered Lean source hash and old selected axiom set must
remain unchanged. New sources require explicit autoImplicit=false EMPTY logs,
full build, expanded standard-only axiom audit and terminal process success.
No sorry/admit/custom axiom, unsafe/native_decide bypass or relaxed heartbeat.
The exact rational source-slab certificate is re-executed/hash checked;
it refutes a displayed volume estimate, not the proposition or goal itself.
'''
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
print(json.dumps(dict(prefix=prefix,modules=modules)))
