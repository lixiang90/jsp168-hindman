from pathlib import Path
import json
import re

prefix = 'round-native-rational-zero-slope-bracket'
old = 'round-native-rational-fractional-bracket-input'
base = json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained = {f['path'] for f in base['files']}
modules = sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules) == 17, modules
components = [
    'ACTUAL [0,1) circle fractional representatives are constructed with exact real-sample/quotient identities and measurability. Off the TRUE coordinate-boundary strip, close points have actual real representative difference EXACTLY equal to circle distance. This is proved from nearest-integer witnesses; discontinuity at zero is not ignored.',
    'TRUE product-circle Haar coordinate-boundary union measure is PROVED <=ofReal(2*dimension*r), using actual measure-preserving coordinate evaluation and canonical circle-ball Haar. All actual fractional expression/slab sets are measurable. Actual torus neighborhood lies in TRUE boundary strip UNION actual widened slab; every real-coordinate difference and circle norm growth is proved.',
    'ACTUAL [0,1) Haar transport is PROVED by exact circle quotient pushforward and AE equality of interval measures, without replacing original samples. The corrected finite-integer-cover slab bound is APPLIED on canonical circle Haar for BOTH signs of nonzero slope. Exact actual offset reduction modulo one precedes all source inputs.',
    'TRUE full product-torus fractional slab measure is PROVED by actual measurable Option coordinate split and Tonelli under SAME canonical product-circle Haar. Actual bounded offsets and finite nearby-integer cover give one fixed K before ALL beta/zeta/tolerances. Budget retains actual card(C)*2*epsilon/abs(zeta_none). No abstract slice-volume bound is supplied as an oracle.',
    'CORRECT full torus neighborhood estimate is PROVED with fixed positive tolerance factor c and radius r depending on coefficient/dimension/actual integer-cover budgets BEFORE all beta/zeta/N. Maximal nonzero selected coordinate controls all growth. Actual boundary and widened-slab Haar measures are combined to prove <=ofReal(delta/2). This repairs the reviewed source numerical estimate; original circle samples remain exact.',
    'Actual distance-to-slab cutoff is a GENUINE UNIT Lipschitz observable with radius r as actual peak height. Its Haar integral is bounded by r times actual neighborhood measure, for any NONEMPTY slab, without assuming closedness. Dense actual hits yield a TRUE discrepancy >=delta*r/2 under canonical Haar. All measurable/integrability/complex-mean and actual unit-family inputs are discharged.',
    'ACTUAL original RANGE-N linear torus inverse for ANY finite index type is PROVED for every actual unit observation, with one fixed natural frequency/error budget before all unbounded real frequencies/N. Genuine compact Fourier selection produces an ACTUALLY NONZERO integer vector; exact real Fourier phase and genuine geometric mean bound give original N^-1 dot-product scale. No new inverse assumption is used.',
    'GENUINE ZERO-linear-slope fractional bracket inverse is PROVED from actual dense original-scale small values for ANY finite index type. It produces either actual REAL coefficient bounds at original N^-1 scale OR an ACTUALLY NONZERO bounded original integer vector with small dot gamma. Actual maximal-coordinate selection, original integer-vector transport, complete frequency-size/dot-product identities and empty/zero coefficient cases are discharged. ALL budgets precede unbounded beta/zeta/gamma and EVERY positive N.',
    'GENUINE FIRST quantitative mixed-frequency alternative of Claim 7.7 is PROVED for unrestricted alpha by APPLYING the proved zero-slope inverse to actual augmented coordinates. It produces all original zeta circle bounds OR an actual pair (k,r), not both zero, with fixed size and original-scale small k dot gamma+r*alpha. This is NOT yet the full SECOND Claim 7.7 alternative.',
    'The FIRST mixed-frequency alternative is APPLIED to SAME actual native fractional parameters/useful shifts, and then to SAME ACTUAL original nonzero Fourier signal. One fixed NATURAL budget before all raw sources retains actual relative character/grid/norm, SAME bounded positive natural M, BOTH higher P/Q tables and actual bounded integer offset. Actual useful density is capped at min(rho,1) and transported by proved finite-set inclusion. General degree has ONLY full actual lower-degree child inverse premise; degree-two FIRST alternative has NO child inverse premise.',
    'Actual mixed output yields the true SECOND small-slope input with original N*abs(nearest-integer residual)<=A, corrected coefficient budget R*(Z+1), and SAME useful-shift error <=R*B, for either sign of r. These facts are PROVED, not premises about a hoped-for bracket inverse. The general small-linear-slope bracket inverse remains OPEN.'
]
remaining = base['last_round']['remaining']
remaining += '\nLATEST PROVED ZERO-SLOPE / FIRST MIXED ALTERNATIVE: The reviewed numerical slab issue is repaired by TRUE canonical-circle fractional transport, signed circle slab estimates, actual product-Haar Tonelli, real representative neighborhood control and explicit boundary/cover/coefficient/dimension budgets. TRUE unit distance cutoff/dense discrepancy and actual RANGE-N torus inverse are PROVED. The ZERO-linear-slope bracket inverse is FULLY PROVED for ANY finite index type, including empty/zero coefficient cases, with actual nonzero integer vector/error/size and fixed budgets before all raw inputs. FIRST unrestricted-alpha mixed alternative is PROVED and APPLIED to original Fourier signal with SAME native relative character/M/offset/higher P/Q tables. Degree-two FIRST alternative has NO child inverse premise. Actual second nearest-integer residual/coefficient/error input is PROVED. NEXT: full SMALL-LINEAR-SLOPE bracket inverse (Proposition 5.3), preserving actual dense shifts via genuine affine slope refinement, fixed fractional-length interval selection, freezing/translation/Haar/original-N comparison as needed. Then apply SECOND time to obtain full Claim 7.7: bounded multiplier making zeta near integers OR actual nonzero small k dot gamma. Original case-(ii) reconstruction already proved; case-(i) actual commutator lattice-integrality/rational denominators OR reducible rational nonlinearity filtration/factorization and genuine degree+nonlinearity induction still required. General inverse, small-N source branches, corrected multivariate inverse, interval Gowers correlation inverse, rough progressions, Alignment and StrongConjecture remain UNPROVED. No unavoidable obstruction; publication/application milestone not reached.'
text = Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
    text = re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),text,flags=re.M)
text = re.sub(r'^"""Audit .*?\n','"""Audit true torus slab geometry, complete zero-slope bracket inverse and actual native FIRST mixed alternative.\n',text,count=1)
text = re.sub(r"reference_scope='[^']*'", "reference_scope='OpenAI quantitative Leibman route; corrected Green-Tao Proposition 5.3 zero-slope geometry and full zero-slope inverse; FIRST Claim 7.7 mixed alternative applied to native signal; general small-slope/SECOND alternative/full target remain open'",text)
needle="    write(PREFIX+'-slab-certificate-result.json',run(['python','bracket-slab-volume-counterexample.py'],PREFIX+'-slab-certificate.txt'))\n"
assert text.count(needle)==1
text = text.replace(needle,needle+"    Path(PREFIX+'-slab-review.json').write_bytes(Path(OLD+'-slab-review.json').read_bytes())\n",1)
Path(prefix+'-audit.py').write_text(text,encoding='utf-8')
review = '''JSP-000168 / Erdos #172: PROVED zero-slope bracket inverse / actual FIRST mixed alternative
Author mathematical review, 2026-10-13. Verdict: Partial coverage.
Previous goal turn: PROGRESS, confirmed by retained registered proof state.
NOT independent kernel replay or external peer review.

Full original positive distinct monochromatic FS/FP target remains OPEN.
Pinned OpenAI six-section source:
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026,
06_rough_progressions. Auxiliary primary route:
https://arxiv.org/html/0709.3562v4 , Proposition 5.3 / Claim 7.7.
Corrected multivariate scope: https://arxiv.org/html/1311.6170v3 .

1. Exact actual fractional geometry
The actual representative is the real value of equivIco(1,0). It is
measurable, lies in [0,1), maps to SAME circle point, and equals Int.fract
on EVERY real source sample, including integers and zero. If ||x||>r and
dist(x,y)<r, round(rep(x)-rep(y)) must be zero: a positive integer would
put rep(x) near one, and a negative integer would put it near zero,
contradicting the ACTUAL boundary distance. Thus the actual real difference
has absolute value EXACTLY dist(x,y). No global continuity of fract is asserted.

2. Actual boundary and neighborhood
Under SAME product-circle Haar, each coordinate-boundary strip has actual
measure ofReal(2r) when 2r<=1. This follows from actual measure-preserving
coordinate evaluation and the proved canonical circle closed-ball measure.
Finite union subadditivity bounds the TRUE boundary union by ofReal(2*m*r).

The actual fractional expression and its circle-norm slab are measurable.
Off the boundary, every real coordinate difference is bounded by the true
Pi distance. Finite-sum triangle bounds give real expression growth at
most m*W*dist when all |zeta_i|<=W. Circle-near-integer and triangle bounds
then put the TRUE r-neighborhood in boundary(r) UNION slab(eps+m*W*r).
The slab need NOT be closed; actual thickening is still open/measurable.

3. TRUE Haar transport and signed circle slices
The actual quotient map from Lebesgue restricted to [0,1) to canonical
circle Haar is measure preserving, proved from the actual Ioc quotient
pushforward and AE equality of interval measures. On EVERY actual [0,1)
point the representative equals the original point, proving exact measure
transport for any measurable real set. Sample representatives are NEVER
changed from Ico to Ioc. Only interval MEASURES are compared AE.

The previously proved real finite-cover slab bound now applies to actual
circle Haar. Negative slope is treated by negating theta and z, retaining
the exact circle norm; no absolute-positive-slope assumption is smuggled in.
The result is card(C)*2*eps/abs(z) with a fixed finite integer box C,
before every bounded theta/z and actual tolerance. z!=0 is explicit.

4. Full product slab measure
For Option indices, the actual measurable split sends torus to
(remaining-coordinate torus) times circle, preserving SAME product Haar.
First reduce beta modulo an ACTUAL integer, exactly on circle values.
For each remaining coordinate sample u, theta=fract(beta)+sum zeta_i*rep(u_i)
has actual bound 1+card(remaining)*Z. Tonelli applies to the actual measurable
slab set. Its circle slice has the PROVED uniform finite-cover bound.
The remaining Haar factor is a probability measure, so integration proves
the TRUE full torus slab bound card(C)*2*eps/abs(zeta_none).
Neither a slice-volume estimate nor Haar transport is supplied as an oracle.

5. Numerical repair with explicit fixed budgets
Let C=actual integer-box cardinality, D=Option index cardinality (>=1),
c=delta/[32*(C+1)*(Z+1)] and r=c/D. Both are positive and fixed BEFORE
ALL beta/zeta/gamma/sample lengths, for Z>=0 and 0<delta<=1.
Let w=abs(zeta_none)>0 and assume this coordinate is maximal. If eps<=c*w,
the widened tolerance E=eps+D*w*r is <=2*c*w, and is <=1 by the TRUE
coefficient-budget factor Z+1. Boundary measure is <=ofReal(delta/16),
widened-slab measure <=ofReal(delta/8). Their sum is <=ofReal(delta/2).
This PROVES the correct full neighborhood bound with fixed radius and
tolerance, repairing the reviewed source numerical issue. The old exact
rational interval certificate is retained/re-executed; it is NOT a
counterexample to the quantitative proposition or full original goal.

6. Actual unit cutoff and discrepancy
F=max(0,r-infDist(x,S)) is an ACTUAL unit Lipschitz real cutoff, with peak r
on S and bounds 0<=F<=r<=1. Its complex observable is in the actual unit
family. For S NONEMPTY, outside actual r-thickening F=0, even when S is not
closed. Integrability, indicator domination and canonical Haar transport
prove integral F<=r*measure(thickening). Dense actual hits yield mean F
>=delta*r. The ACTUAL finite complex mean and integral are real-valued,
so actual discrepancy is >=delta*r/2 when the neighborhood measure is
<=ofReal(delta/2). Empty-set infDist behavior is never used incorrectly:
nonnullity of S is actually deduced from positive useful density.

7. True original-range linear torus inverse
For ANY finite index type, the actual compact unit family provides a fixed
nonzero Fourier-selection threshold and fixed frequency budget. Exact
Fourier phase equality gives the genuine n*(k dot gamma) real phase on
SAME Finset.range(N), not a replacement cube. The proved geometric mean
inverse yields original N^-1 dot-product scale. A fixed natural budget
absorbs both frequency size and phase error BEFORE ALL gamma/N/observables.
The integer vector is ACTUALLY NONZERO; this is not a named inverse premise.

8. Complete ZERO-slope bracket inverse
For Option indices with maximal selected coordinate, either N*w<=B/c,
giving actual real coefficient bounds for EVERY coordinate, or eps=B/N<=c*w.
In the latter case the actual dense circle bound is EXACTLY actual slab
membership on SAME linear orbit. The PROVED cutoff discrepancy and actual
linear torus inverse PRODUCE a nonzero integer vector with bounded size
and original N^-1 dot product. All positive N are covered.

For arbitrary finite indices, zero coefficient vector gives the first
alternative directly (including empty indices). Otherwise an ACTUAL maximal
coordinate is selected. A true Option/subtype equivalence reindexes samples,
coefficient sums and frequencies. Finite simultaneous budgets before choosing
the maximal coordinate give ONE fixed original budget. Original integer
vector nonzeroness, complete natAbs size and exact real dot product survive.
Thus the ZERO-linear-slope bracket inverse is FULLY PROVED for ANY finite
index type, without a bracket/inverse oracle, bounded beta/gamma assumptions,
or any unsupported power law in delta.

9. FIRST Claim 7.7 alternative, not full Claim 7.7
For UNRESTRICTED alpha, actually adjoin its frequency with coefficient ONE
and slope ZERO. Exact prior augmentation preserves original circle values;
the augmented coefficient budget is max(Z,1). APPLY the now PROVED zero-slope
inverse. Either all actual original zeta circle values have N^-1 bounds,
or an ACTUAL pair (k,r), not both zero, has bounded size and
 N*norm(k dot gamma+r*alpha)<=A.
Frequency-size/dot-product decomposition is proved on actual coordinates.
This FIRST alternative is quantitative, not an assumed analytic interface.
It is NOT the full SECOND alternative with a zeta multiplier OR small
nonzero k dot gamma alone.

10. SAME native Fourier signal and correction
The first alternative is applied to the ACTUAL native bracket parameters
and useful shifts. True V subset range(N) and bound predicate inclusion
transport density, without assuming all shifts or changing N. Then the
native signal theorem COMPOSES the previously PROVED actual dense Fourier
packet with this actual quantitative alternative. Density is capped at
min(rho,1), BEFORE raw sources. One fixed NATURAL budget absorbs character
norm, original higher P/Q tables, integer-offset and mixed-frequency/error
budgets. SAME actual relative character/finite list, positive bounded
natural M and BOTH higher P/Q coefficient tables are preserved.
General degree still has only FULL desired lower-degree child inverse.
Degree-two FIRST native alternative discharges that child premise by the
actual degree-one base; it is not the full original degree-two inverse.

The actual mixed output gives the TRUE second input: nearest-integer residual
has N*abs<=A, corrected coefficients r*zeta-k have budget R*(Z+1), and
every SAME natural useful shift has corrected bracket error <=R*B. These
are proved for either sign of r. A positive Z assumption is unnecessary
in this algebraic correction and is not retained as an unused premise.

11. Remaining goal
Next prove the full SMALL-LINEAR-SLOPE bracket inverse, using actual affine
slope refinement and genuine fixed fractional-length interval selection/
freezing/translation/Haar and original-N comparison when needed. Then apply
it SECOND time to obtain full Claim 7.7. The prior original reconstruction
already handles an actual nonzero small k dot gamma vector with BOTH complete
raw coefficient tables. For case (i), actual commutator character lattice
integrality/rational denominators and reducible nonlinearity filtration/
factorization still require proof. Complete degree+nonlinearity induction,
small-N source branches, corrected multivariate inverse, separate interval
Gowers correlation inverse, rough progressions, Alignment and final original
positive distinct FS/FP remain OPEN. No unavoidable obstruction found.
Public repository/PR/prize application milestone has NOT been reached.

All old registered proof-source hashes and selected axiom sets are retained.
All new modules must pass explicit autoImplicit=false with EMPTY logs,
full build, expanded selected axiom audit and final terminal process checks.
Only propext/Classical.choice/Quot.sound allowed; no sorry/admit, custom
axiom, unsafe/native_decide bypass or relaxed heartbeat configuration.
'''
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
print(json.dumps(dict(prefix=prefix,modules=modules),ensure_ascii=False))
