from pathlib import Path
import ast

PREFIX = 'round-native-rational-multiparameter-inverse'
OLD = 'round-native-rational-unit-inverse'
MODULES = [
    'Hindman168/NativeRationalLinePolynomial.lean',
    'Hindman168/FiniteComplexIntegerRangeMean.lean',
    'Hindman168/NativeRationalLineDiscrepancy.lean',
    'Hindman168/NativeRationalLineCharacterProduction.lean',
    'Hindman168/NativeRationalCommonLineCharacter.lean',
    'Hindman168/FiniteDirectionLabelThinning.lean',
    'Hindman168/NativeRationalLineConstantRecovery.lean',
    'Hindman168/LeibmanCompleteDirectionalCoefficients.lean',
    'Hindman168/NativeRationalDenseDirectionReconstruction.lean',
    'Hindman168/NaturalDivisionLengthBounds.lean',
    'Hindman168/NativeRationalConstantMvDiscrepancyAnchor.lean',
    'Hindman168/NativeRationalLargeMvToAllLengths.lean',
    'Hindman168/NativeRationalMultiparameterLargeInverse.lean',
    'Hindman168/NativeRationalMultiparameterInverse.lean',
    'Hindman168/NativeRationalFiniteVariablesInverse.lean',
]
COMPONENTS = [
    'ACTUAL native multivariable short lines are constructed by scalar affine substitution term by term, with true rational-filtration weights and exact orbit, scalar projection, coefficient and canonical Haar discrepancy identities. The unconditional Unit inverse now PRODUCES a true original nonzero horizontal/grid/norm character and both line tables in ONE finite original character pool fixed before every raw source/basepoint/direction/length.',
    'The corrected bounded complex equal-cube averaging argument now obtains ONE SAME actual original character on dense directions and dense original basepoints. Genuine scalar multivariable small-value inverse recovers all positive line constant coefficients with one bounded positive multiplier per direction. Exact finite multiplier thinning and simultaneous homogeneous integer reconstruction produce ONE SAME scaled original nonzero character for BOTH COMPLETE raw original coefficient tables. The scalar budget precedes direction size, so no circular choice of constants is used.',
    'A positive explicit floor lower bound and fixed minimum line threshold close ALL large original equal-cube lengths. Empty original character pools make actual discrepancy impossible; they do not manufacture a character. Genuine actual sample anchors generalize the proved constant-source argument to arbitrary finite variables, closing ALL original short positive lengths without character-existence or inverse premises.',
    'UNCONDITIONAL NativeRationalWeightedInverseStatement D L sigma is now PROVED for EVERY finite variable type sigma and every actual native datum/rational Lie filtration. It includes degree zero, empty variable types, every positive original N, actual original nonzero horizontal/grid/norm character and BOTH COMPLETE original monomial/binomial tables. No native/scalar/line inverse or production premise remains. This is the corrected fixed-data existential multiparameter inverse, not explicit delta-power laws, a Gowers correlation inverse or final FS/FP target.',
]
REMAINING = (
    'StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
    'The full original positive distinct rapidly separated monochromatic finite sums/products is the prize target. '
    'The COMPLETE unconditional native rational-filtration inverse is now proved for EVERY finite variable type, '
    'degree and positive original equal-cube length, with actual original nonzero horizontal/grid/norm character '
    'and BOTH COMPLETE raw original coefficient tables. Unit degree/natural nonlinearity induction, actual '
    'native line sources, true complex averaging, same-character dense rows, genuine scalar constant recovery, '
    'common multiplier thinning, all-degree directional reconstruction and true short-length anchors are composed. '
    'Remaining: separate interval Gowers correlation inverse, rough progressions, cube/Alignment and final '
    'StrongConjecture. Fixed-data existential constants do not certify explicit source delta-power laws. '
    'Only true positive exponential lattice powers are used, not Exp(y) lattice membership. '
    'Author build/hash/axiom/source review is not independent kernel replay or external peer review. '
    'The repaired source slab estimate is not an unavoidable obstruction. Public repository/PR/prize '
    'milestone has not been reached.'
)
source = Path(OLD + '-audit.py').read_text(encoding='utf-8')
lines = source.splitlines(keepends=True)
replacements = dict(PREFIX=PREFIX, OLD=OLD, MODULES=MODULES, COMPONENTS=COMPONENTS, REMAINING=REMAINING)
for node in reversed(ast.parse(source).body):
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno] = [name + ' = ' + repr(replacements[name]) + '\n']
source = ''.join(lines).replace(
    'unconditional complete native rational-filtration Unit inverse with genuine degree/nonlinearity induction and all original positive lengths; corrected multiparameter inverse and final target remain open',
    'unconditional complete corrected native rational-filtration inverse for every finite variable type and positive original length; separate Gowers correlation inverse and final target remain open')
Path(PREFIX + '-audit.py').write_text(source, encoding='utf-8')
Path(PREFIX + '-mathematical-review.txt').write_text('''JSP-000168 mathematical/application review, 2026-10-13

Classification: PROGRESS. Complete corrected native multiparameter inverse is
proved with fixed-data existential constants. StrongConjecture remains UNPROVED.
This is author-side application review and Lean build/axiom checking, not
independent replay or external mathematical peer review.

1. Actual short lines. Each vector source term is mapped by the genuine scalar
eval2Hom affine substitution C(x_j)+C(q_j)*X(). Degree nonincrease and true
L.antitone retain weighted membership; no coefficient-size bound is assumed.
All-real evaluation identities imply literal native integer orbit equality.
Scalar projection has the exact scalarUnitPolynomial/line polynomial and
positive coefficient identities. Actual Nat range, integer interval and Unit
cube finite means agree, including the empty mean. Subtracting the canonical
Haar integral inside a mean is used only for positive length. No quotient-
sample equality is asserted to imply vector/source equality.

2. Finite original characters. The proved unconditional Unit inverse at
delta/2 fixes Q before ALL p,x,q,H. The original grid image to continuous
linear maps is filtered by norm<=Q. Membership preserves original nonzero
horizontal lattice character and norm. For a true centered complex short-line
discrepancy it produces an actual member, ALL positive monomial line rows and
the FULL binomial Unit table. These outputs are not analytic oracle premises.

3. Corrected common-character averaging. f(x)=F(orbit(p,x))-canonical Haar mean
is globally bounded by 2 from the unit observable/probability integral. The
original actual cube discrepancy is its exact finite mean. Boundary averaging
and finite common-character selection use deltaLemma=delta/2 and B=2, so the
line production threshold is delta/2. The short line may leave the original
cube, as permitted by the proved globally bounded averaging lemma. The output
is ONE original character on a dense direction set and dense original
basepoints. Explicit equality of the two cube Finsets handles instance
presentation without changing sampling or probability measures.

4. Recovery and integer labels. Original weighted scalar degree<=ell follows
from the true terminal layer=bottom, including potentially high-degree zero
vector terms. Each positive r<=ell line coefficient is a basepoint polynomial
of degree<=ell-1. The PROVED scalar multivariable small-value inverse includes
the CONSTANT coefficient and gives one M_q<=B^(ell+1) for ALL positive r.
This uses the genuine small tolerance Q/H<=mu/10 and N>=B. Exact finite
pigeonhole thinning to one positive M retains direction count after a factor
B^(ell+1). Overlapping labels are allowed; no falsely unique choice is used.

5. Complete reconstruction. Exact homogeneous directional sums at x=0 and
simultaneous integer reconstruction give one positive multiplier for EVERY
degree 1..ell. The direction set has count ell*K^n < card*K. Above-degree
original rows vanish. Actual H>=tau*N transfers ALL positive raw ORIGINAL
monomial bounds; complete integer Stirling conversion gives the binomial
table. Both use the SAME scaled original character mult*M*chi. Positive
integer scaling preserves nonzero, horizontal integrality and norm; original
grid membership is proved under the enlarged fixed budget. No row-dependent
character or discarded binomial/constant data substitutes for the output.

6. Constants and ALL large lengths. Q fixes the finite character pool A.
For A nonempty, mu=(delta/2)/(8*card A) is positive and <=1. B is chosen before
K, so choosing K>16*(n+ell*B^(ell+1)*card A+1)/delta is not circular. Direction
reconstruction then fixes C before raw sources. tau=1/(2*K^2). The elementary
floor inequality gives floor(N/K^2)>=N/(2*K^2) for N>=K^2. A fixed threshold
absorbs B, K^2 and ceil(10Q/mu), proving true short-line length and tolerance.
If A is empty, common-character selection contradicts emptiness; this branch
asserts no fake positive density or character. Every cap is an actual natural
number chosen before p,N,F. No source delta-power claim is made.

7. ALL short lengths and all finite variables. A true positive original finite
discrepancy has an actual sample anchor at least as large as its mean. A true
weighted constant vector polynomial through it retains that discrepancy at
EVERY positive equal-cube length, even for empty variable types. Calling only
the already proved large-N theorem at its fixed threshold supplies a bounded
original nonzero character. Original scalar degree and circle norm<=1 bound
all original short-N rows; exact Stirling transfer covers the complete
binomial table. Degree zero has its genuine registered base. Literal variable
renaming by Fintype.equivFin transfers weights, exact native original cube
discrepancy, both coefficient tables and SAME original character.

8. Exact final scope. The public theorem is
Hindman168.native_rational_weighted_inverse_finite_variables D L sigma :
  NativeRationalWeightedInverseStatement D L sigma
for EVERY legitimate native D/rational Lie filtration L and finite sigma.
It requires NO inverse, line-production, scalar-phase, character or Gowers
premise. Every delta>0, ONE budget before all raw sources/observables, every
original positive N, original nonzero/norm/grid horizontal character, and
BOTH COMPLETE positive original monomial/binomial tables are included.

9. Remaining goal and review boundary. This is a fixed-data existential
quantitative equidistribution inverse. It does not prove the distinct interval
Gowers nilsequence correlation inverse or explicit delta-power laws needed by
some source estimates. Rough progression comparison, cube/Alignment and final
positive distinct rapidly separated monochromatic FS/FP remain open. The
repaired original source slab estimate is not a terminal obstruction. Old
registered proof hashes/axioms, six pinned OpenAI source sections and exact
rational slab certificate are rechecked. Public repository/PR/prize milestone
has not been reached; original mathematical and Lean authorship differ.
''', encoding='utf-8')
print(PREFIX)
