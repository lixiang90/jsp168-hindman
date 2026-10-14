from pathlib import Path
import json,re
prefix='round-native-rational-polynomial-recursion'
old='round-native-rational-weighted-relative'
base=json.loads(Path('verification-manifest.json').read_text(encoding='utf-8'))
retained={f['path'] for f in base['files']}
modules=sorted(p.as_posix() for p in Path('Hindman168').glob('*.lean') if p.as_posix() not in retained)
assert len(modules)==11,modules
components=[
 'ONE actual original compact coset representative set is SELECTED for every true native datum, before ALL source coefficients and integer shifts. Actual representative/original lattice factors and their exact factorizations are CONSTRUCTED; original nonnormal lattice is unchanged. True native logarithms on this compact set have a fixed finite bound.',
 'ACTUAL coefficient-dependent basepoint representative, original lattice-linear correction and integer-shift representative now construct a true normalized coefficient polynomial. Corrected P(1) belongs to SAME fixed compact set. Original sample equality, genuine weights/normalized logarithmic zero/ordinary degree ell and exact shift-power lattice factorization are PROVED for ANY original rational Lie filtration.',
 'BOTH coordinates of ACTUAL chosen normalized integer relative pair are explicitly identified with ORIGINAL unnormalized integer coset samples, under actual translations r*t and r. This yields exact original complex observable derivative samples for ANY observable, without an assumed normal lattice or coefficient bound.',
 'ACTUAL compact normalization then weighted relative/terminal reduction constructs a true zero-trim polynomial in SAME degree-reduced native data and actual projected IMAGE filtration, with weight zero, degree ell-1, exact integer group/coset factor samples, COMPLETE scalar pullback polynomial and EVERY projected aggregate vector coefficient.',
 'Zero-vector removal is PROVED to retain COMPLETE scalar polynomials and EVERY aggregate vector/scalar coefficient. The actual initial polynomial state trims arbitrary zero-vector terms, preserving ALL original evaluations/coset samples/scalar polynomials while obtaining genuine ordinary degree ell from original weights and terminal zero.',
 'GENUINE finite POLYNOMIAL recursion is NOW CONSTRUCTED. Every actual state contains actual native data/finite rational filtration/coefficient polynomial with PROVED weight zero and ordinary degree; successor uses actual compact choices and original relative/terminal reduction. Bound after n stages is ell-n; EVERY integer successor sample is actual preceding-stage normalized pair projected through true factor map. At ell stages actual group is SUBSINGLETON and actual orbit equals identity coset.',
 'ALL actual recursive GEOMETRY is PROVED fixed before source coefficients and shift choices. Full packed actual group/model/lattice/chart/metric/filtration datum at every stage equals a geometry-only primitive recursion depending on original D,F,n. Changing original polynomial or ALL shift choices leaves that actual packed geometry unchanged; this is not a presumed uniformity interface.',
 'Actual chosen compact normalizations retain COMPLETE original horizontal scalar polynomial and EVERY original nonconstant horizontal coefficient modulo integers against SAME original lattice. These statements apply to every actual recursive native datum; existence of an ORIGINAL NONZERO inverse character is still open.',
 'At the ACTUAL terminal group the specified-metric canonical native Haar discrepancy is PROVED zero for ANY continuous observable and ANY NONEMPTY finite sample. This uses actual native quotient probability, not a replacement measure. Empty sample is explicitly excluded because its average would be zero rather than the constant observable value.',
 'FULL genuine finite POLYNOMIAL recursion is APPLIED to ORIGINAL ordinary-degree <=d univariate source at SAME original stretch d. Actual initial samples/scalar polynomials are retained, actual stage degree is s*d-n, and actual group is trivial at s*d stages. Original coefficients and original lattice logarithms remain UNBOUNDED; geometry/polynomial/base-case termination does not yet imply quantitative inverse.'
]
remaining=base['last_round']['remaining']
needle='NEXT: actual iterated weighted polynomial/orbit recursion using these normalizations and true relative/quotient stages; recursive orbit discrepancy/canonical Haar/specified metric/finite-unit/nonzero frequency transport;'
assert needle in remaining
replacement='NOW actual iterated WEIGHTED POLYNOMIAL recursion is CONSTRUCTED at bound ell-n, with genuine compact representative/lattice normalization choices, all original pair coordinate/observable samples, complete scalar and aggregate coefficient preservation, true image weights/degree and exact EVERY-stage integer quotient factor samples. ALL actual stage group/model/lattice/chart/metric/filtration GEOMETRY is PROVED fixed before original coefficients and ALL shifts, equal to geometry-only recursion. At ell stages actual group/orbit is trivial and actual specified-metric canonical native Haar discrepancy is ZERO for every NONEMPTY finite sample. The FULL polynomial recursion is APPLIED to ORIGINAL degree <=d input at SAME stretch d, degree s*d-n and termination at s*d. NEXT: genuine arbitrary rational-filtration terminal torus/nonzero Fourier branches, recursive orbit discrepancy/canonical Haar/specified metric/finite-unit/nonzero frequency transport beyond the proved terminal base case;'
remaining=remaining.replace(needle,replacement)
x=Path(old+'-audit.py').read_text(encoding='utf-8')
for name,value in [('PREFIX',prefix),('OLD',old),('MODULES',modules),('COMPONENTS',components),('REMAINING',remaining)]:
 x=re.sub('^'+name+r' = .*$',lambda m:name+' = '+repr(value),x,flags=re.M)
x=x.replace('Audit arbitrary actual weighted relative polynomial reconstruction, true projected polynomial degree reduction, generic normalizations and original normalized source application.','Audit actual compact normalization choices, genuine finite weighted polynomial recursion, fixed original recursive geometry, exact original pair samples and actual canonical terminal discrepancy.')
x=x.replace('actual arbitrary weighted relative reconstruction and true quotient polynomial degree drop proved; recursive nonzero inverse/full prize theorem open','actual finite polynomial recursion/fixed geometry/compact choices/original samples/terminal canonical discrepancy proved; general nonzero-frequency induction/full prize theorem open')
Path(prefix+'-audit.py').write_text(x,encoding='utf-8')
review='''JSP-000168: actual compactly normalized polynomial recursion and fixed geometry
Author mathematical review, 2026-10-13. Not independent kernel replay or external peer review.

Route: six retained OpenAI sections at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
especially 06_rough_progressions and Green--Tao section 7, Proposition 7.2:
https://arxiv.org/html/0709.3562v4 . Corrected equal-side scope:
https://arxiv.org/html/1311.6170v3 . Original coefficients remain UNBOUNDED.

1. Actual fixed compact original coset set comes from proved openness,
   local compactness and original coset quotient compactness. Actual choices
   include original lattice factors and exact g=r*gamma, with no normality
   of the lattice. Compactness/continuous native Log proves a finite bound
   on chosen representatives, NOT on lattice factors or original coefficients.
2. Actual source-dependent r, gamma0, gamma1 and t are selected only AFTER
   the native datum's fixed compact set. Actual corrected P(1) equals the
   compact representative of true basepoint-normalized P(1), so it really
   is bounded even for unbounded source coefficients. Its integer h power
   is exactly t*gammah for actual original lattice gammah. Negative h is
   included. True normalization weights use SAME F, not re-stretching.
3. The actual normalized relative pair's first coordinate after r*t action
   equals ORIGINAL sample at n+h, and its second coordinate after r action
   equals ORIGINAL sample at n. This uses original nonnormal coset equality
   and actual lattice factors, retaining exact complex derivative samples
   for arbitrary observables. No Fourier mean/invariance assumption is
   needed for the sample algebra; descent of observables remains separate.
4. Actual compactly normalized relative coefficient polynomial projects
   through true terminal quotient. Removing zero-vector terms retains
   every actual evaluation, COMPLETE scalar polynomial and EVERY aggregate
   vector/scalar coefficient. Actual ordinary degree ell-1 follows from
   the SAME projected image terminal layer; input coefficients may remain
   arbitrarily large. Exact group/coset integer factor samples are proved.
5. Initial arbitrary weighted coefficient list is zero-trimmed, preserving
   actual original samples and full scalar polynomials. F(ell+1)=bottom
   proves degree <=ell even if the raw source representation has high
   degree scalar terms attached to zero vectors. No invalid source termwise
   ordinary-degree assumption is introduced.
6. Actual state is a sigma of NativeData, a true finite rational filtration
   and an actual polynomial with PROVED weights/ordinary degree. Successor
   is fully constructed from actual normalizations and relative/terminal
   quotient backend. No degree-drop, inverse or orbit-compatibility field
   is postulated. Primitive recursion carries true polynomials at EVERY
   stage, degree bound ell-n, and exact EVERY-stage predecessor pair samples.
7. The geometry stripping map erases polynomial and normalization choices.
   Direct induction proves the ENTIRE actual packed NativeData/filtration
   equals a geometry-only recursion depending just on original D,F,n. Thus
   group/model/lattice/chart/metric and EVERY filtration layer are fixed
   BEFORE ALL original coefficients and shift choices. This is necessary
   for later fixed-data compact/frequency/finite-unit bounds; it is PROVED,
   not inferred from syntactic similarity of the recursive constructions.
8. At ell stages bound is zero; top initial group layer equals bottom
   terminal group layer. The ACTUAL native group is subsingleton and all
   actual polynomial coset samples are identity. Scalar normalization
   formulas retain complete original horizontal polynomial and EVERY
   original nonconstant coefficient modulo integers for every lattice-
   integral horizontal functional. These formulas do not assert existence
   or nonzeroness of an inverse character.
9. Terminal discrepancy base case uses ACTUAL native quotient probability
   and ACTUAL specified metric topology. Quotient is subsingleton by
   surjectivity of original coset map, hence each continuous observable
   is constant. Integral equals that constant by probability normalization;
   the NONEMPTY finite average also equals it. Empty samples are excluded:
   claiming zero discrepancy for them would in general be false.
10. Original ordinary degree <=d source feeds this FULL actual polynomial
    recursion with weights from SAME original stretch d. Initial trimming
    retains exact original samples/scalar polynomials; every stage degree
    is s*d-n and group triviality occurs at s*d. No enlarged stretch s*d,
    substitute coordinate lattice or bounded original coefficient input
    is assumed. This is genuine polynomial/orbit recursion and terminal
    analytical base case, not a complete quantitative inverse induction.

Review boundary: arbitrary rational-filtration terminal torus/nonzero
Fourier branches, canonical Haar/discrepancy/unit/frequency induction and
ORIGINAL NONZERO horizontal-character reconstruction with finite-list/
operator/binomial bounds are still open. Corrected multivariate and interval
Gowers correlation inverse, rough progression descent, cube conditional
laws/posterior/positive Alignment and final FS/FP theorem remain open.
StrongConjecture is UNPROVED; no unavoidable obstruction is established.
Public repository/PR/prize application remain pending the requested milestone.

Exact remaining record:
'''+remaining+'\n'
Path(prefix+'-mathematical-review.txt').write_text(review,encoding='utf-8')
ds=[(k,n) for m in modules for k,n in re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([A-Za-z][A-Za-z0-9_.]*)',Path(m).read_text(encoding='utf-8'),re.M)]
print(json.dumps({'modules':len(modules),'theorems':sum(k in {'theorem','lemma'} for k,n in ds),'definitions':sum(k in {'def','abbrev'} for k,n in ds)}))
