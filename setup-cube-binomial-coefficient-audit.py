from pathlib import Path
prefix = 'round-cube-binomial-coefficient'
old = 'round-native-cube-character'
modules = ['Hindman168/'+n+'.lean' for n in ['CubePolynomialFacePart','CubeBinomialCoefficient','CubeBooleanExpansion','CubeTaylorNoCancellation','NativeResidueCubeScalarCoefficient']]
components = [
'Constructed exact increment-support face parts of arbitrary real multivariate polynomials, proved their coefficients, support, sum recovery and degree bound, and vanishing for faces larger than the polynomial degree. Empty faces and dimension zero are included.',
'Proved the coefficient formula for a univariate polynomial evaluated at the sum of base/increment variables. Constructed actual binomial face polynomials and the isolated monomial, with exact support, total degree and factorial/multinomial identity.',
'Proved the Boolean binomial expansion by evaluating actual vertex restrictions: killing absent increment variables keeps exactly those face parts contained in the vertex. This is an equality for all real variables, not an expansion assumption.',
'Proved the isolated coefficient of the explicit scalar Taylor/face sum is c(j,A)/(j-card(A))!. Other faces cannot contribute because increment supports differ; lower orders have insufficient total degree; higher orders vanish under the derived maximal-face tail.',
'Instantiated that explicit scalar polynomial with the SAME-source actual Taylor coefficients and ACTUAL rational-residue cube horizontal functional. Derived its exact isolated coefficient and escape for every fixed nonzero rational multiple. Equality with the horizontal projection of the actual group-valued cube and cube adaptation remain unproved.'
]
remaining = ('StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
'Original q=0 weak probability limit, SAME-filtration actual cube group, rational filtration, '
'rational-residue orbit/Haar probability with full support and cube invariance, and actual horizontal '
'cube obstruction to original maximal rational face-level character are proved. The actual Boolean '
'binomial expansion and no-cancellation coefficient identity for the explicit scalar Taylor/face sum '
'are now proved; its coefficient escapes by SAME-source irrationality. Remaining: identify that '
'explicit scalar sum with the horizontal projection of the ACTUAL group-valued cube and prove '
'original source cube adaptation; simultaneous local cube laws through ORIGINAL s+1 with length '
'before locality; projected face invariance/full support, joint lifts/full Alignment; separate '
'arbitrary-input GTZ interval Gowers LINEAR nilsequence inverse; final positive distinct rapidly '
'separated SAME-color ALL nonempty FS AND FP. No source/Haar/character/inverse oracle or new axiom '
'introduced. Author checks are not independent kernel replay or external peer review. Private '
'checkpoint repository created at user request; keep PRIVATE. Public repository/PR/prize milestone '
'not reached.')
for source, target in [('verification-manifest.json',prefix+'-baseline.json'),('lakefile.toml',prefix+'-lakefile-before.toml')]:
    dest=Path(target)
    if dest.exists(): assert dest.read_bytes()==Path(source).read_bytes()
    else: dest.write_bytes(Path(source).read_bytes())
source=Path(old+'-audit.py').read_text(encoding='utf-8')
replacements={'PREFIX=':prefix,'OLD=':old,'BASELINE=':prefix+'-baseline.json','MODULES=':modules,'COMPONENTS=':components,'REMAINING=':remaining}
lines=[]
for line in source.splitlines():
    key=next((k for k in replacements if line.startswith(k)),None)
    lines.append(key+repr(replacements[key]) if key else line)
source='\n'.join(lines)+'\n'
source=source.replace(old+'-lakefile-before.toml',prefix+'-lakefile-before.toml')
Path(prefix+'-audit.py').write_text(source,encoding='utf-8')
Path(prefix+'-mathematical-review.txt').write_text('''Author mathematical review, 2026-10-14.
Pinned OpenAI section 7: Boolean binomial expansion and isolated coefficient.

The variables are Option(Fin d), with none the base variable and some k the
kth increment. cubeIncrementSupport records exactly the increments with
positive exponent. cubePolynomialFacePart filters the actual coefficient
finsupp by this exact support. Hence coefficients and support are literal
identities, and summing over ALL faces recovers the original polynomial.
Cardinality of increment support is bounded by total monomial degree.
Filtering never raises total degree, so faces of size above the degree vanish.
These arguments include empty faces, degree zero and cube dimension zero.

For arbitrary univariate P, evaluating at the sum of variables has coefficient
P.coeff(total monomial degree) times the monomial's multinomial coefficient.
This follows from the actual power-of-sum coefficient formula and a finite
sum over P.support, including the case of an absent coefficient. Applying
it to the existing scalarBinomialPolynomial proves degree <= j. The selected
exponent is j-card(A) on the base and one on precisely A. Under card(A)<=j
its degree is j; a factorial multiplication identity proves its coefficient
is 1/(j-card(A))!, with nonzero denominators justified by factorial positivity.

Vertex restriction replaces absent increment variables by zero, preserving
the base variable. A monomial survives iff its increment support is contained
in the vertex. This proves the actual polynomial evaluation identity and
then the Boolean expansion of binomial(b0+sum increments,j), for ALL real b.
No equality about group multiplication is assumed or inferred here.

cubeTaylorFaceScalarPolynomial is explicitly a finite scalar sum. At the
selected monomial only face A contributes. Taylor orders below j vanish by
their proved total-degree bound. Orders above j vanish by the supplied
maximal-level tail on faces of cardinality <= k; card(A)<=j<k ensures the
condition. The coefficient of order j is exactly c(j,A)/(j-card(A))!.
The theorem requires j<N, so its selected order is really in the sum.

The native instantiation uses the existing ACTUAL residue cube functional
and SAME original polynomial Taylor residuals, with N=ell+1. Source adaptation
proves each Taylor vector belongs to F_k; the previously derived all-face
maximal-level kernel therefore supplies the tail, not a new oracle. The
existing irrationality escape theorem transfers along the exact coefficient
identity for every nonzero rational multiple. No extension of irrationality
to an unrelated source or enlargement of original degree/step occurs.

IMPORTANT LIMIT: This is an escaping coefficient of the explicitly defined
scalar face/Taylor sum. Equality of this sum with the horizontal projection
of the actual group-valued cube has NOT yet been proved. Actual original
cube polynomial adaptation is also outstanding. Thus quantitative Leibman
cannot yet be applied to obtain the requested simultaneous cube laws.
Alignment, the separate arbitrary-input GTZ inverse and final same-color
FS/FP theorem remain outstanding. StrongConjecture UNPROVED, goal ACTIVE.
No unavoidable obstruction established. Author audit is not independent
kernel replay or external peer review. Keep user-requested repository PRIVATE.
''',encoding='utf-8')
print(prefix)
