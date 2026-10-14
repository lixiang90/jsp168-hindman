from pathlib import Path
import json
import re

prefix = 'round-native-rational-fractional-bracket-input'
old = 'round-native-rational-first-layer-coordinates'
base = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained = {f['path'] for f in base['files']}
modules = sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules) == 11, modules
components = [
    'ACTUAL compact fractional bracket parameters gamma/zeta/beta/alpha are CONSTRUCTED from SAME normalized source, SAME relative character and SAME common NATURAL M. Beta includes the actual common integer-offset correction. Geometry-only gamma budget and zeta budget precede ALL raw source coefficients; scaled |zeta_i|<=S*A*B is PROVED using M<=S and norm(chi)<=A.',
    'The COMPLETE actual paper beta/alpha/sigma CIRCLE bound is transported EXACTLY to the actual fractional bracket on SAME V subset U with ONE common actual integer offset. Positive geometry-only density rho/card(C) is PROVED from actual cardinality inequality. The original N^-1 scale, original samples, true representatives and exact NATURAL multiplier are preserved.',
    'Actual NONZERO original Fourier signal is APPLIED to the bounded fractional bracket input with fixed character/operator/offset/frequency/coefficient/density/multiplier/sample-threshold budgets before ALL raw source inputs. BOTH original higher P/Q monomial and paper-binomial tables, SAME actual relative horizontal character and ALL combined coefficient bounds on actual refined shifts are RETAINED. General degree has ONLY FULL actual lower-degree child inverse premise; degree-two input has NO child inverse premise.',
    'EVERY original real functional killing ACTUAL F_2 projects a TRUE weighted RAW source to an AFFINE scalar polynomial. Every higher aggregate coefficient is killed using actual weighted submodule membership; no bound on individual source terms is assumed. SAME compact normalized scalar is genuinely LINEAR because its true zero coefficient is zero. Its first coefficient equals actual original Log character at SAME compact source first value.',
    'Actual candidate k dot gamma equals the RAW original first scalar coefficient MODULO an actual lattice integer, discharged by original compact-normalization coefficient preservation and genuine candidate lattice integrality. Actual higher RAW monomial coefficients vanish. COMPLETE nonconstant raw monomial bounds for EVERY Unit multiindex follow from actual small k dot gamma; no restriction to j<=ell is needed.',
    'BOTH COMPLETE original raw monomial and ACTUAL multivariate paper-binomial coefficient tables are reconstructed for EVERY positive Unit multiindex. The existing genuine INTEGER tensor-Stirling bound applies inside the original ell box; outside-box coefficients vanish by an ACTUAL Stirling weight argument. One fixed positive NATURAL budget before ALL raw sources/sample lengths/actual vectors yields TRUE original nonzero horizontal character, actual operator bound, original finite grid and BOTH complete tables. This FULL Claim-7.7-(ii) reconstruction has NO child inverse premise; extracting k from the bracket signal remains OPEN.',
    'Claim 7.7 FIRST augmentation is PROVED as an exact circle identity: adjoining alpha as a frequency with coefficient ONE and linear slope ZERO retains the actual original circle value. The augmented coefficient budget is max(Z,1), before unbounded alpha. Claim 7.7 SECOND correction uses an ACTUAL nearest-integer residual with absolute value EXACTLY original circle norm. The actual integer correction of zeta/alpha preserves the scaled bracket circle value at NATURAL shifts, with explicit |r| original-scale error bound for either sign of r.',
    'Fresh source review finds the displayed slab volume upper bound in Proposition 5.3 cannot be used unchanged. An exact RATIONAL interval certificate at delta=1/100, zeta=100, theta=0 gives actual slab length 1/5, exceeding displayed delta/2=1/200. This is author interval arithmetic, NOT Lean measure formalization, NOT a counterexample to the proposition itself and NOT an unavoidable obstruction. Source estimate is NOT silently accepted as a hypothesis.',
    'CORRECT one-dimensional affine integer-slab measure bound is NOW formally PROVED in Lean with TRUE finite integer-cover cardinality: volume(S)<=ofReal(card(C)*2*epsilon/z) for z>0. Its true delta/2 condition is PROVED with the cover budget retained. A fixed integer box before ALL bounded offsets/slopes/tolerances is CONSTRUCTED from actual nearest-integer witnesses, giving an actual bounded-circle-slab measure theorem. Full torus boundary/neighborhood/Fubini/discrepancy work remains OPEN.'
]
remaining = base['last_round']['remaining']
remaining += '\nLATEST FRACTIONAL BRACKET INPUT / RECONSTRUCTION MILESTONE: Actual bounded gamma/zeta/beta/alpha and SAME refined useful density/circle relation are APPLIED to the true Fourier signal, retaining BOTH higher P/Q tables and original relative character/M/grid/combined bounds. Degree-two fractional input has NO child inverse premise. FULL original univariate inverse conclusion from an ACTUAL bounded nonzero small k dot gamma vector is PROVED, including BOTH COMPLETE raw original monomial/Mv-binomial tables, true nonzero/horizontal/lattice/operator/finite-grid properties and ONE fixed natural budget. Extraction of k remains OPEN. Exact Claim 7.7 augmented-coordinate and centered integer-correction circle/error algebra is PROVED. Source Proposition 5.3 slab bound has an exact rational author counterexample; correct one-dimensional finite-cover slab measure bound is PROVED in Lean. NEXT: full torus slab boundary/neighborhood/Fubini/discrepancy argument with CORRECT coefficient/finite-cover budgets, quantitative bracket lemma and Claim 7.7, then actual case-(i) commutator character lattice integrality/rational denominators OR reducible rational nonlinearity filtration/factorization and genuine degree+nonlinearity induction. General inverse, small-N, corrected multivariate inverse, interval Gowers correlation inverse, rough progressions, Alignment and StrongConjecture remain UNPROVED. Source numerical issue is not an unavoidable obstruction; publication/application milestone not reached.'
text = Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
    text = re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),text,flags=re.M)
text = re.sub(r'^"""Audit .*?\n','"""Audit actual fractional bracket input, full original first-layer reconstruction, centered correction and corrected slab measure.\n',text,count=1)
text = re.sub(r"reference_scope='[^']*'", "reference_scope='OpenAI quantitative Leibman route; Green-Tao section 7 actual Claim 7.7 input/case-(ii) reconstruction/algebra; Proposition 5.3 displayed slab estimate reviewed and corrected one-dimensional bound proved; full bracket alternative remains open'",text)
text = text.replace('    results = []\n', "    write(PREFIX+'-slab-certificate-result.json',run(['python','bracket-slab-volume-counterexample.py'],PREFIX+'-slab-certificate.txt'))\n    results = []\n",1)
extra = '''    certificate = obj(PREFIX+'-slab-review.json')
    cr = obj(PREFIX+'-slab-certificate-result.json')
    assert cr['terminal'] and cr['exit_code']==0 and cr['log_sha256']==digest(cr['log'])
    assert cr['command']==['python','bracket-slab-volume-counterexample.py']
    assert certificate['violates_displayed_volume_bound'] and not certificate['refutes_proposition_itself'] and not certificate['unavoidable_obstruction']
    from fractions import Fraction as F
    xs = [(F(i['left']),F(i['right']),i['nearby_integer']) for i in certificate['intervals']]
    assert len(xs)==101 and sum((b-a for a,b,k in xs),F(0))==F(1,5)>F(1,200)
    assert all(xs[j][1]<xs[j+1][0] for j in range(100))
    assert all(abs(100*a-k)<=F(1,10) and abs(100*b-k)<=F(1,10) for a,b,k in xs)
    assert certificate['exact_slab_volume']=='1/5' and certificate['displayed_upper_bound']=='1/200'
'''
text = text.replace('    return baseline,files,summary,fixed\n',extra+'    return baseline,files,summary,fixed\n',1)
text = text.replace("    write(PREFIX+'-review.json',review);", "    review.update(source_slab_certificate=PREFIX+'-slab-review.json',source_slab_certificate_sha256=digest(PREFIX+'-slab-review.json'),source_slab_script_sha256=digest('bracket-slab-volume-counterexample.py'))\n    write(PREFIX+'-review.json',review);",1)
Path(prefix+'-audit.py').write_text(text,encoding='utf-8')
review = '''JSP-000168 / Erdos #172: ACTUAL fractional bracket input and original reconstruction
Author mathematical review, 2026-10-13. Verdict: Partial coverage.
Previous goal turn: PROGRESS, verified by retained registered proof state.
NOT independent kernel replay or external peer review.

The full original positive distinct monochromatic FS/FP target remains OPEN.
Pinned OpenAI six-section source:
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026,
06_rough_progressions. Auxiliary primary route:
https://arxiv.org/html/0709.3562v4 , Proposition 5.3 / Claim 7.7 and case (ii).
Corrected multivariate scope: https://arxiv.org/html/1311.6170v3 .

1. Genuine parameters from SAME source
gamma=H(P_0(1)), zeta_i=M*commutatorCoefficient_i, alpha=M*secondBinomial(Q),
beta=M*P(1)+sum zeta_i*b_i. All definitions refer to ACTUAL compact normalized
source P_0, ACTUAL relative character, ACTUAL nonlinear Q and SAME natural M.
The offset correction is present, not dropped. Actual compact first-value
membership gives the fixed frequency bound. Operator norm plus M<=S and
norm(chi)<=A gives one fixed |zeta_i|<=Z=S*A*B. Z can be zero; no nonzero
commutator coefficient is inferred from relative-character nonzeroness.

2. Actual density and circle bound transported
The original finite-offset box is fixed before all raw sources. Actual
finite witness refinement supplies SAME V subset U, V nonempty, with
card U <= card C * card V. C nonempty gives its positive cardinality and
therefore a positive geometry-only rho'=rho/card C. The original useful
density rho*N<=card U implies rho'*N<=card V by a checked real division
identity. No N is rescaled. The PROVED exact scalar bracket identity carries
the original N*norm(M*(beta+alpha*h+sigma(h))) bound to SAME fractional
bracket at every h in V, using ACTUAL beta/alpha/zeta/gamma parameters.

3. Native signal application and exact scope
The new native theorem composes the genuine paper scalar separation with
the PROVED refinement and geometry-only parameter bounds. The signal is
the SAME actual original nonzero Fourier mean. Its original lower-degree
inverse premise is retained in GENERAL degree. ALL source geometry,
normalizations, observations, relative character, original finite grid,
operator bound, M positivity/bound, higher P/Q monomial/BOTH binomial tables,
true original scale and EVERY combined coefficient bound on V are proved.
Fixed A/B/rho/H/Z/S/T/K and the character grid precede every RAW source,
sample length and original unit observation. The degree-TWO native input
discharges the FULL child inverse using the actual proved degree-one base.
No quantitative bracket alternative is supplied as an oracle or claimed solved.

4. TRUE F_2 gives affine original scalar
For ANY actual real functional f killing L.layer(2), actual aggregated
weighted coefficient membership gives coeff_j in L.layer(j) for j>=2.
Antitonicity puts it in L.layer(2), so f(coeff_j)=0. A polynomial coefficient
proof now gives the exact affine polynomial, with constant and linear
coefficients retained. The compactly normalized source has genuine zero
at the origin, so its scalar is exactly linear. Evaluating at one and
using true native Exp/Log identities gives its first coefficient as
f(Log(P_0(1))). This proof includes cancellations in vector-list terms;
it never assumes each raw coefficient term bounded or individually zero.

5. COMPLETE actual case-(ii) original reconstruction
Take the actual integer-coordinate functional f_k. Previous proofs establish
f_k kills F_2, is original-lattice integral and is nonzero when k!=0.
Actual compact normalization preserves its nonconstant coefficients modulo
an actual lattice integer. The normalized first coefficient is f_k(Log a),
which is EXACTLY sum k_i*gamma_i. Therefore the original RAW first scalar
coefficient equals this dot product MODULO Z. All original RAW higher scalar
coefficients vanish. An ACTUAL small dot-product bound hence proves the
COMPLETE raw monomial table for EVERY positive Unit multiindex, not just
indices <=ell and not only the normalized polynomial.

For the actual Mv paper-binomial table, apply the checked integer tensor
Stirling norm estimate inside the ell box at multiplier one and lower index
one. Outside that box the Unit index exceeds ell; every actual Stirling
weight is zero, proved term by term. This proves the COMPLETE original
binomial table for EVERY positive Unit multiindex with a fixed finite budget.
Finally one fixed positive natural Q absorbs candidate operator norm, raw
monomial and raw binomial budgets. The ACTUAL candidate lies in the original
finite horizontal grid at Q. The theorem has EXACT full original univariate
inverse output: nonzero/horizontal/operator/grid and BOTH COMPLETE tables.
Its input is an ACTUAL bounded nonzero integer vector with small dot gamma.
No child inverse premise is needed for reconstruction. EXTRACTING that
vector from the fractional bracket signal remains UNPROVED.

6. Exact Claim 7.7 augmentation and second correction
Adjoin one coordinate of frequency alpha and coefficient ONE, with new
linear slope ZERO. The augmented bracket equals the original real bracket
minus floor(h*alpha), so its circle value is EXACTLY the original value.
The actual coefficient budget is max(Z,1), despite unrestricted alpha.
This establishes the algebra needed for the FIRST bracket-lemma use.

For the SECOND use, let a=r*alpha+sum k_i*gamma_i and replace it by
a-round(a). Its absolute value is EXACTLY the actual UnitAddCircle norm
of a, including when [0,1) fract(a) would be close to one. Set new
zeta_i=r*zeta_i-k_i and beta'=r*beta. For NATURAL h, the corrected bracket
differs from r times the original bracket by the ACTUAL INTEGER
-h*round(a)+sum k_i*floor(h*gamma_i). Circle values are therefore equal.
The checked integer-weighted circle norm bound gives error <=|r|*B at
SAME original N scale, for both signs of r. No false real-multiplier norm
principle or absolute-smallness claim for ordinary Int.fract is used.
These are algebra/error results, not the missing quantitative alternatives.

7. Fresh source numerical issue, not an unavoidable obstruction
The source's displayed slab volume bound before (5.10)-(5.11) cannot be
used unchanged. In ONE dimension choose delta=1/100, zeta=100, theta=0.
Then |zeta|=1/delta and its displayed tolerance delta*|zeta|/10 is 1/10.
On [0,1], the condition norm(100*t)<=1/10 consists of 101 disjoint clipped
intervals centered at k/100. Interior intervals have width 1/500; the two
end intervals have width 1/1000. Their exact total length is 1/5, exceeding
the displayed delta/2=1/200. Enlarging the set cannot reduce its measure.
The retained certificate checks all exact rational endpoints, disjointness,
endpoint affine bounds and total interval length. This is author interval
arithmetic, NOT a Lean measure proof of the counterexample. It does NOT
refute Proposition 5.3, whose fixed-degree/budget powers permit a corrected
small tolerance and neighborhood radius. No unavoidable obstruction found.

8. Correct measure step formally proved
The new Lean lemma proves a TRUE one-dimensional slab estimate. If S has
an actual finite nearby-integer cover C and z>0, each relevant affine slab
lies in the actual closed interval [(k-theta-eps)/z,(k-theta+eps)/z].
Measure monotonicity and finite union subadditivity, followed by actual
Lebesgue interval volumes, prove
 volume(S)<=ofReal(card(C)*2*eps/z).
The exact sufficient condition card(C)*2*eps <= (delta/2)*z now PROVES
volume(S)<=ofReal(delta/2), with the integer-cover budget retained.

For |theta|<=T, |z|<=Z, t in [0,1] and eps<=1, actual nearest-integer
witnesses have |k|<=T+Z+1. One natural K>T+Z+1 before ALL actual inputs
provides the fixed finite cover [-K,K]. Thus a genuine bounded-circle-slab
measure bound is formally PROVED. This remains one-dimensional and z>0;
negative slopes, torus boundaries, neighborhood bounds, product/Fubini
transport and discrepancy detection are NOT claimed finished.

9. Full remaining goal
Next prove corrected torus slab boundary/neighborhood/Fubini/discrepancy
arguments and the true Proposition 5.3 / Claim 7.7 alternatives. Apply the
now completed original reconstruction to case (ii). In case (i), actual
commutator character lattice integrality/rational denominators still require
proof because split-basis exponential points are not asserted lattice.
Then handle true reducible rational nonlinearity filtration/factorization,
degree+nonlinearity induction and small-N completion. Corrected multivariate
inverse, separate interval Gowers correlation inverse, rough progressions,
Alignment/positivity and final original positive distinct FS/FP remain OPEN.
No public repository/PR/application milestone has been reached.

Every old registered proof source/hash and selected axiom set is retained.
All new modules must pass explicit autoImplicit=false checks with EMPTY logs,
full build and selected axiom audit, with final terminal processes awaited.
Only standard propext/Classical.choice/Quot.sound are allowed; no sorry,
admit, custom axiom, unsafe or native_decide implementation bypass.
'''
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
print(json.dumps(dict(prefix=prefix,modules=modules),ensure_ascii=False))
