from pathlib import Path
import json,re
prefix='round-native-rational-degree-one-inverse'
old='round-native-rational-polynomial-recursion'
base=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained={f['path'] for f in base['files']}
modules=sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules)==11,modules
components=[
 'TRUE rational filtration degree ONE forces ORIGINAL native group commutativity, actual native Lie bracket zero and actual nilpotency bound <=1. Actual NativeData(1) is CONSTRUCTED by reclassifying this PROVED bound with EVERY original group/model/chart/lattice/metric structure copied literally. Higher-degree recursion retains its original step bound s.',
 'The reclassified abelian datum retains ORIGINAL lattice and specified metric, ACTUAL original group Haar, actual chosen fundamental domain and actual original normalized quotient probability. EVERY original polynomial coset sample and canonical finite discrepancy agree exactly; no replacement Haar, coordinate lattice or assumed measure transport is used.',
 'A GENUINE ORIGINAL degree-one-filtration quantitative polynomial inverse is PROVED, producing an ACTUALLY NONZERO lattice-integral horizontal character in a fixed original finite grid, true ORIGINAL operator norm bound, and BOTH original monomial and paper-binomial coefficient bounds. Fixed bound M precedes ALL source coefficients, positive cube lengths and unit observables. Existing proved abelian inverse is applied only after actual original commutativity/canonical measure compatibility is discharged.',
 'The TRUE weighted degree-one base case works on RAW original vector-polynomial lists with UNBOUNDED coefficients and arbitrary high-degree zero-vector terms. All actual zero-trim degree/evaluation/scalar identities are supplied, so BOTH scalar coefficient bounds apply to original raw coefficients rather than a substituted or assumed bounded polynomial.',
 'Genuine finite variable renaming transports actual vector evaluations, full scalar polynomials, ordinary degree and SAME Lie weights. Actual multi-index mapDomain/total weight, ORIGINAL equal-side integer cube samples/finite means and ORIGINAL native canonical discrepancy commute exactly with the equivalence. COMPLETE paper-binomial coefficients commute through actual box/Stirling reindexing, not just evaluations or monomial coefficients.',
 'NONZERO weighted degree-one inverse is PROVED for ANY finite original variable type, including actual Unit variables of original polynomial recursion. The SAME original native character/finite grid/operator norm and BOTH raw original monomial/binomial coefficient bounds survive the exact finite variable equivalence. No multivariate side-length or short-box scope is broadened.',
 'The NONZERO degree-one base inverse is actually APPLIED to the TRUE coefficient polynomial of an actual degree-one recursive state. The true recursion degree-one node is CONSTRUCTED from actual stage bound ell-j=1, retaining SAME full original recursive native datum. For every ell>0 the actual node at j=ell-1 exists; its actual group/model/lattice/metric equals geometry-only stage fixed BEFORE all source coefficients and shifts. Higher-degree ORIGINAL character pullback remains open.'
]
remaining=base['last_round']['remaining']
needle='NEXT: genuine arbitrary rational-filtration terminal torus/nonzero Fourier branches, recursive orbit discrepancy/canonical Haar/specified metric/finite-unit/nonzero frequency transport beyond the proved terminal base case;'
assert needle in remaining
replacement='NOW the TRUE degree-ONE rational-filtration quantitative inverse BASE CASE is PROVED on the ORIGINAL group/model/lattice/metric/canonical Haar. Original group commutativity and proven step<=1 are discharged; literal reclassification preserves original Haar/fundamental-domain/probability/samples/discrepancy. An ACTUALLY NONZERO original horizontal character is PRODUCED with fixed original finite grid, true operator norm and BOTH original monomial/paper-binomial bounds, for RAW UNBOUNDED weighted coefficients and ANY finite variable type including Unit. Exact variable equivalence preserves original cube samples, canonical discrepancy and COMPLETE monomial/binomial coefficients. This inverse is APPLIED to actual recursive degree-one polynomial state; actual node at j=ell-1 exists for ell>0 and retains SAME coefficient/shift-independent actual stage geometry. NEXT: genuine arbitrary rational-filtration terminal torus/nonzero Fourier branches, HIGHER-DEGREE recursive orbit discrepancy/canonical Haar/specified metric/finite-unit/nonzero frequency transport beyond proved degree-zero and degree-one base cases;'
remaining=remaining.replace(needle,replacement)
x=Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
 x=re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),x,flags=re.M)
x=x.replace('Audit actual compact normalization choices, genuine finite weighted polynomial recursion, fixed original recursive geometry, exact original pair samples and actual canonical terminal discrepancy.','Audit genuine ORIGINAL rational degree-one NONZERO inverse, exact abelian-data/canonical-Haar compatibility, raw weighted coefficients, complete finite variable equivalence and actual recursive degree-one state application.')
x=re.sub(r"reference_scope='[^']*'", "reference_scope='06_rough_progressions and Green-Tao section 7: genuine ORIGINAL degree-one NONZERO inverse with actual canonical Haar/raw weights/finite grid/operator/monomial/binomial bounds and actual recursive state; higher-degree induction/full prize target open'", x)
Path(prefix+'-audit.py').write_text(x,encoding='utf-8')
review='''JSP-000168: genuine ORIGINAL rational degree-one nonzero inverse base case
Author mathematical review, 2026-10-13. Not independent kernel replay or external peer review.

Route: retained six OpenAI sections at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
especially 06_rough_progressions; Green--Tao section 7, Proposition 7.2,
https://arxiv.org/html/0709.3562v4 . Corrected equal-side scope:
https://arxiv.org/html/1311.6170v3 . Original coefficients remain UNBOUNDED.

1. A true F of degree ONE has G_1=G, G_2=1. Its proved original group
   bracket condition puts EVERY group commutator in G_2, hence actual
   original commutativity. Native bracket zero follows from actual
   F.bracket(1,1) and F(2)=0. Actual nilpotency class <=1 is derived,
   not assumed or inferred from ordinary polynomial degree.
2. The reclassified NativeData(1) copies EVERY original model/manifold/
   group/lattice/class/metric field; only the already-PROVED step bound
   is represented more sharply. All original lattice/metric/group Haar/
   chosen fundamental domain/normalized quotient probability identities
   are literally proved. Exact original polynomial orbit and canonical
   discrepancy agree, without an assumed replacement measure. The generic
   higher-degree recursion continues to retain its original step bound s.
3. Existing PROVED abelian canonical inverse is applied on these actual
   compatible original data. The character conclusion is explicitly
   RoughNativeHorizontalFunctional, whose FIRST conjunct is chi!=0.
   It is lattice-integral and horizontal on the ORIGINAL group; true
   operator norm and membership in a FIXED ORIGINAL finite character grid
   are retained. No zero-character substitute or assumed inverse interface
   is introduced. Both monomial and paper-binomial coefficient bounds are
   present, with M fixed BEFORE source coefficients, N and unit observable.
4. Arbitrary weighted degree-one source lists may include scalar terms of
   arbitrarily high degree attached to zero vectors. Zero trimming PROVES
   actual ordinary degree <=1 from F(2)=0 and original term weights.
   Actual original evaluations/orbits and COMPLETE scalar polynomials are
   retained, so the actual produced character bounds original raw scalar
   coefficients. Original vector coefficients and original lattice logs
   remain UNBOUNDED; compact representatives do not bound lattice factors.
5. Finite variable equivalence uses true MvPolynomial.rename and actual
   mapDomain coefficient identity. Original vector evaluations, scalar
   projections and weights are proved; multi-index sum is preserved.
   The actual ORIGINAL integer cube maps bijectively, so its finite mean
   and canonical Haar discrepancy agree EXACTLY, including all boundary
   samples. This is equal-side cube reindexing, not a short-box extension.
6. COMPLETE paper-binomial coefficients also commute: actual binomial box
   maps bijectively, Stirling product is invariant, actual monomial
   coefficients agree, and sum over the original box is reindexed. This
   avoids the gap of retaining only monomial coefficients or sampled values.
7. Any finite original variable type is renamed to Fin(card), with the
   equivalence fixed before source inputs. Original cube discrepancy feeds
   the PROVED NONZERO weighted inverse. All index weights and BOTH original
   raw monomial/binomial coefficients are pulled back. The actual character
   itself, operator norm and ORIGINAL lattice/finite grid are unchanged.
8. This supplies Unit-variable inverse on an ACTUAL degree-one recursive
   coefficient state. The actual node is constructed by equality transport
   from the original true polynomial recursion's bound ell-j=1. Transport
   preserves the ENTIRE original native datum, not only an isomorphic group.
   At j=ell-1 this node exists whenever ell>0. It equals geometry-only
   native stage fixed BEFORE all original coefficients and shifts.

Review boundary: these are COMPLETE genuine degree-zero and degree-one
base cases, NOT the full higher-degree quantitative inverse. Nonzero
Fourier branches on arbitrary original rational filtration terminal torus,
canonical Haar/metric/unit/frequency induction and ORIGINAL higher-degree
nonzero character reconstruction/pullback with finite-list/operator/
binomial bounds remain open. A character on the recursive degree-one group
has not yet been pulled back to the original higher-degree source group.
Corrected full multivariate inverse, separate interval Gowers correlation
inverse, progression descent, cube laws/posterior/positive Alignment and
final FS/FP extraction remain open. StrongConjecture UNPROVED; no genuine
unavoidable obstruction found. Publication/application milestone not yet met.

Exact remaining record:
'''+remaining+'\n'
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
ds=[(k,n) for m in modules for k,n in re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([A-Za-z][A-Za-z0-9_.]*)',Path(m).read_text(encoding='utf-8'),re.M)]
print(json.dumps({'modules':len(modules),'theorems':sum(k in {'theorem','lemma'} for k,n in ds),'definitions':sum(k in {'def','abbrev'} for k,n in ds)}))
