from pathlib import Path
prefix='round-native-cube-source'
old='round-cube-binomial-coefficient'
modules=['Hindman168/'+n+'.lean' for n in ['NativeFiniteProductCoordinateLinear','NativeCubeTaylorFaceVector','NativeCubeTaylorFactorPolynomial','NativeCubeSourcePolynomial','NativeCubeSourceProjection','NativeResidueCubeSourcePolynomial','NativeResidueCubeActualCoefficient','NativeResidueCubeBoundedPolynomial']]
components=[
'Constructed actual internal cube Taylor face vectors and proved their ORIGINAL max-level membership, exact vertex coordinates and agreement with actual cube face functionals. Inadmissible faces are zero.',
'Constructed each internal Taylor factor from the actual Boolean face polynomials. Proved weighted adaptation, exact original vertex exponentials and full scalar projection; oversized faces vanish by the proved binomial degree bound.',
'Constructed the full ordered cube polynomial with actual BCH multiplication, preserving original weighted adaptation at every stage. Proved every vertex equals the original Taylor product, and at ell+1 equals the SAME original source for every real cube input.',
'Proved horizontal projection of actual weighted polynomial products is additive, using actual commutator annihilation. The actual ordered cube polynomial therefore projects to exactly the explicit scalar face/Taylor sum.',
'Transported the source construction to the ACTUAL rational-residue cube with unchanged original group and filtration. Proved filtered-polynomial adaptation, exact original vertices and projection identity, including semantic Taylor-residual invariance under changing the rational conjugated lattice.',
'Proved one maximal original face/level simultaneously bounds the ENTIRE actual horizontal projection degree by j, identifies its isolated coefficient with the ORIGINAL Taylor value divided by (j-card(A))!, and forces escape for every nonzero rational multiple.',
'Removed only zero vector terms to obtain an actual cube log-polynomial representation of degree at most ORIGINAL ell, without changing values or any horizontal projection. This supplies the degree-bounded input needed for quantitative box obstruction theorems.'
]
remaining=('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
'Original point laws, actual cube geometry and Haar measures, Boolean binomial coefficient isolation, '
'and the SAME-source ACTUAL rational-residue cube polynomial are proved. Its original vertices, '
'filtered adaptation, horizontal projection identity, maximal projection degree and isolated coefficient '
'escape are now proved; a zero-trimmed degree-ell representation preserves all values and projections. '
'Remaining: connect all cube variables to the spatial box-obstruction interface and prove fixed '
'progression/translation top-coefficient transport, then derive simultaneous local cube laws through '
'ORIGINAL s+1 with length before locality; projected face invariance/full support, joint lifts/full '
'Alignment; separate arbitrary-input GTZ interval Gowers LINEAR nilsequence inverse; final positive '
'distinct rapidly separated SAME-color ALL nonempty FS AND FP. No source/Haar/character/inverse '
'oracle or new axiom introduced. Author checks are not independent kernel replay or external peer '
'review. Keep the user-requested GitHub repository PRIVATE. Public repository/PR/prize milestone '
'not reached.')
for source,target in [('verification-manifest.json',prefix+'-baseline.json'),('lakefile.toml',prefix+'-lakefile-before.toml')]:
    dest=Path(target)
    if dest.exists(): assert dest.read_bytes()==Path(source).read_bytes()
    else: dest.write_bytes(Path(source).read_bytes())
replacements={'PREFIX=':prefix,'OLD=':old,'BASELINE=':prefix+'-baseline.json','MODULES=':modules,'COMPONENTS=':components,'REMAINING=':remaining}
lines=[]
for line in Path(old+'-audit.py').read_text(encoding='utf-8').splitlines():
    key=next((k for k in replacements if line.startswith(k)),None)
    lines.append(key+repr(replacements[key]) if key else line)
source=('\n'.join(lines)+'\n').replace(old+'-lakefile-before.toml',prefix+'-lakefile-before.toml')
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
Path(prefix+'-mathematical-review.txt').write_text('''Author mathematical review, 2026-10-14.
Pinned OpenAI section 7: actual cube polynomial, adaptation, scalarization.

The linear coordinate maps are on the ACTUAL iterated product model. Their
application theorem identifies them with the existing native coordinates,
so later linear sums/smul calculations do not assume a coordinate oracle.
For v in ORIGINAL F_k, a face vector for A with card(A)<=k is the explicit
upper-face Lie array embedded into the ACTUAL internal cube model. It belongs
to internal layer k because max(k,card(A))=k. For inadmissible faces it is zero.
All coordinates and evaluations by arbitrary cube functionals are proved.

A single Taylor factor is a finite vector polynomial with the proved
cubeBinomialFacePolynomial k A as scalar entries. Each has degree <=k,
and the face vector lies in layer k, so antitonicity gives weighted adaptation.
At a vertex, the sum equals binomial(b0+sum present increments,k) times v,
by the actual Boolean identity. Inadmissible faces contribute zero because
their scalar polynomial is zero; no illegal face generator is used.
Internal exponential/inclusion/coordinate identities therefore identify
the factor with the ORIGINAL Taylor factor at every real input.

The full source polynomial uses actual roughNativeProductMvPolynomial
recursively, in the same order as adaptedTaylorOrderedProduct, including
order zero. Its weighted adaptation follows from the proved internal cube
filtration product theorem. Its exponential has EXACT original Taylor product
at each vertex. At ell+1 the original residual terminal theorem gives the
SAME source, without replacing or refactorizing it. Step s and filtration
length ell retain the original values, independently of cube dimension.

Horizontal projection of an actual BCH polynomial product is additive:
weighted evaluations lie in initial layer zero, and actual horizontal
commutator annihilation makes the BCH commutator correction vanish. This is
proved via the genuine original logarithm-product theorem, not assumed as
an interface. Induction then gives the full explicit scalar Taylor/face sum.

Rational-residue cube data changes the lattice but retains the original
model/group and every original filtration layer. The actual source is built
on this conjugated data. The original vertex and filtered-polynomial identities
are proved. Crucially, Taylor residual code is NOT simply assumed to be
syntactically identical after this change: native_conjugate_taylor_residual_eval
proves semantic equality for every index and real argument via the actual
removal evaluation recurrence. The projection identity therefore uses the
ORIGINAL Taylor coefficients controlled by source irrationality.

Maximality gives vanishing on all faces of every higher Taylor level. Thus
all higher-order terms of the scalar sum vanish; surviving terms have degree
at most j. This degree bound holds for the ENTIRE horizontal projection,
not just one coefficient, and is essential for later translation invariance.
The same selected j,A gives the isolated coefficient identity and escape
for every fixed nonzero rational multiple. Empty faces and dimension zero
are retained, and factorial denominators remain explicit.

Weighted cube adaptation does not by itself assert the raw list has bounded
ordinary degree, because high-degree entries may have zero vectors. The
bounded representation removes ONLY those zero entries. Terminal layer ell+1
then proves degree <=ORIGINAL ell; all real evaluations and every scalar
projection are unchanged. The logarithm identity is with the actual source.

REMAINING LIMIT: no local cube equidistribution theorem is claimed yet.
All b0 and increment variables must be made spatial in the existing box
obstruction API (its Option none is a separate fixed parameter). Fixed
progression and translation transport of the TOP coefficient is still needed.
Then finite-character obstruction/irrationality contradiction, simultaneous
cube laws through original s+1, smooth-factor transport, projected faces,
joint lifts/Alignment, GTZ arbitrary-input inverse and final FS/FP remain.
StrongConjecture UNPROVED; goal ACTIVE; no unavoidable obstruction established.
No additional axioms or source/Haar/character/inverse oracles introduced.
Author audit is not independent kernel replay or external peer review.
The user requested a PRIVATE repository for travel; keep it PRIVATE.
''',encoding='utf-8')
print(prefix)
