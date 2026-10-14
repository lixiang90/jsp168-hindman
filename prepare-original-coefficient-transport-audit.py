from pathlib import Path
import ast

PREFIX = 'round-native-rational-original-coefficient-transport'
OLD = 'round-native-rational-character-child-signal'
MODULES = [
    'Hindman168/RoughAffineCommonMultiplier.lean',
    'Hindman168/RoughAffineCoefficientRecovery.lean',
    'Hindman168/ScalarRightFactorCoefficientTransport.lean',
    'Hindman168/MvCompleteBinomialTransfer.lean',
    'Hindman168/NativeHorizontalNaturalMultiplier.lean',
    'Hindman168/NativeRationalOriginalCoefficientTransport.lean',
    'Hindman168/NativeRationalUniformOriginalTransport.lean',
    'Hindman168/NativeRationalConstructedChildInverseTransport.lean',
]
COMPONENTS = [
    'Actual affine child coefficients now recover ALL ORIGINAL monomial coefficients at original scale using ONE positive NATURAL period^degree multiplier, exact affine coefficient identities, genuine retained length and signed integer untranslation. Above-degree rows vanish. Circle norms are never divided by the progression step.',
    'ALL positive REAL error coefficients are controlled from the original degree/zero-linear bounds, including outside the degree. Actual horizontal scalar factor identity and genuine rational-factor coefficient integrality prove ORIGINAL monomial transport with common multiplier period^(degree+1). The rational term vanishes modulo one; the REAL error is bounded explicitly. No summand smallness is inferred from a circle norm.',
    'Positive natural scaling preserves actual ORIGINAL nonzero horizontal lattice integrality, norm and original finite-grid budget. Integer tensor Stirling weights convert ALL original positive monomial rows to BOTH COMPLETE ORIGINAL tables, including binomial indices outside the degree box.',
    'For bounded M<=S, q<=B, direction norm<=B and child character norm<=C, ONE ORIGINAL Q budget is chosen BEFORE every raw child character/source/sample. Actual conjugated child horizontal integrality, literal affine child construction, ALL-real source factors, REAL error bounds and actual child coefficient bounds compose to a true ORIGINAL horizontal/grid/nonzero character and BOTH full original coefficient tables under Q. Child coefficient bounds still must be derived by genuine future degree/nonlinearity IH; no same-degree child inverse or full native inverse is assumed or proved.',
]
REMAINING = (
    'StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. '
    'The full original positive distinct rapidly separated monochromatic finite sums/products is the prize target. '
    'Actual finite-character geometry/UNIT child-signal budgets and exact constructed child sources are retained. '
    'Quantitative step/translation/retained-length/REAL-error/rational-coefficient transport now returns BOTH '
    'COMPLETE raw ORIGINAL coefficient tables with true nonzero horizontal/grid character and ONE uniform '
    'budget preceding bounded child characters and all raw sources, PROVIDED actual child coefficient bounds '
    'are derived by legitimate IH. No same-degree inverse is assumed. Remaining: actual canonical finite-child '
    'inverse budgeting from lexicographic IH, genuine well-founded degree+nonlinearity induction, all original '
    'small-N cases and full native inverse Fourier assembly. P first/full diagonal alternative, corrected '
    'multivariate inverse, separate interval Gowers correlation inverse, rough progressions, cube/Alignment '
    'and final StrongConjecture remain OPEN. Fixed-data existential constants are distinct from explicit '
    'delta-power laws. Only true positive exponential lattice powers are used, not Exp(y) lattice membership. '
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
    'simultaneous original finite-character budgets, constructed child UNIT signal, exact horizontal scalar transport identities; quantitative coefficient transport, induction and final target remain open',
    'complete original coefficient transport from actual constructed child coefficients, with uniform original character/grid/two-table budget; child IH, complete native inverse and final target remain open')
Path(PREFIX + '-audit.py').write_text(source, encoding='utf-8')
Path(PREFIX + '-mathematical-review.txt').write_text('''JSP-000168 mathematical/application review, 2026-10-13

Classification: PROGRESS. No full native inverse, no StrongConjecture, and no
unavoidable obstruction is asserted. This is author-side review, not independent
kernel replay or external peer review.

1. Original affine recovery. Exact ring-hom composition and diagonal scaling
coefficients prove child_i=period^i*translated_original_i. Multiplication by
period^d yields period^(d-i)*child_i for i<=d. The latter is NATURAL, so its circle
norm is bounded by natural multiplication. The SAME period^d works in every row.
For i>d, actual degree kills the row. Genuine T>=tau*N transfers child bounds
to ORIGINAL scale N, uniformly with tau^(-d), not coefficient-specific constants.
Signed integer untranslation uses abs(a)<=N and the original fixed-support
translation theorem. Constants never involve polynomial coefficients.

2. Original source factors. The registered ALL-real scalar identity follows from
actual ordered group factorization via the true horizontal logarithm character.
Rational coefficients become integer after period=M*q, using true Exp(y)^q in
Gamma and original horizontal integrality. Extra period^d multiplies those
integers. Real error is bounded by period^d*q*abs(kappa(y))*AE using the ORIGINAL
M*N^i*abs(E_i)<=AE bounds. E_1=0 handles the first row and actual degree handles
all higher rows outside j. No real smallness is inferred from circle smallness;
no separate term is inferred small from a small sum.

3. Original character. period^(d+1)>0 preserves nonzeroness. Horizontal commutator
annihilation is preserved by linearity; actual Gamma values stay integer. Its
norm is exactly period^(d+1)*norm(kappa). Original-grid membership follows from
the proven original lattice/norm criterion. Arbitrary genuine conjugated child
horizontal data are transferred back by the original conjugation-invariance
theorem, without assuming that Gamma is normal.

4. Complete original tables. Actual monomial recovery covers EVERY positive Unit
multiindex, including above d. Integer tensor Stirling conversion bounds all
positive binomial rows at the same original N; outside the degree box all tensor
weights are zero. In the actual application the weighted original source has
degree ell, so the ell-binomial table is the original full expansion. No missing
linear coefficient, top-degree-only table, or child-only table is substituted.

5. Uniform quantifiers. Given fixed S/B/AK/AE/C, period<=S*B and
abs(kappa(y))<=norm(kappa)*norm(y)<=C*B. All norm and two-table budgets fit one
explicit real upper bound, then one positive natural ceiling Q. Q is chosen
BEFORE M/q/kappa/y/p/N. The composed native theorem consumes ACTUAL literal
child construction, genuine factors/errors and actual child coefficients to
return an original nonzero character/grid and BOTH tables under Q.

6. What remains. The child coefficients are valid transport inputs, not an
oracle theorem or assumed same-degree inverse. They MUST be supplied by true
lexicographic degree/nonlinearity IH on legitimate canonical finite child data.
That IH, uniform finite-child constants, full original small-N cases and native
Fourier assembly remain open. Final rough progression/cube/Alignment and FS/FP
target remain open. Fixed existential constants do not certify the source's
explicit delta-power laws. No prize eligibility/publication milestone reached.

7. Source alignment. This supplies the actual progression and rational/error
character transport needed by the pinned quantitative Leibman route used in
OpenAI section 06. All six source sections are hash-compared to pinned objects.
The older exact slab counterexample concerns a repaired intermediate bound;
its exact arithmetic is rechecked, and it is not a terminal obstruction.
''', encoding='utf-8')
print(PREFIX)
