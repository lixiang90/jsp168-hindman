from pathlib import Path
import ast
import re

source = Path('round-rough-exact-division-audit.py').read_text(encoding='utf-8')
modules = ['RoughDenominatorSubring', 'RoughSubringPolynomialDivision', 'RoughSmoothQuotient',
    'RoughSmoothDenominatorSupport', 'RoughInterpolationIntegerValues', 'RoughInterpolationValueError']
components = [
    'RoughDenominatorSubring constructs the actual subring of rational numbers cleared by some power of W, with proofs of all ring operations. Divisibility of a denominator by W^k gives membership, and an inverse of a nonzero smooth integer belongs. Primorial-rough power multiplication being integral forces a member itself to be integral.',
    'RoughSubringPolynomialDivision proves coefficient membership in an arbitrary rational subring is preserved by monic polynomial quotient. Normalizing t+mX to X+t/m and multiplying the quotient by m^(-e) proves that an exact quotient stays in the subring if t and m inverse belong. It uses actual polynomial lifts and map_divByMonic, not a quotient denominator assumption.',
    'RoughSmoothQuotient obtains original R coefficient membership from its integer clearing certificate, proves every coefficient of the exact affine-power quotient is smooth, proves every integer evaluation remains smooth, and then proves quotient integer evaluation whenever the affine progression value is rough and the original R evaluation is integral.',
    'RoughSmoothDenominatorSupport derives m dividing a primorial power from the literal prime-factor smoothness condition, and derives reduced rational denominator prime support from subring membership. The exact quotient therefore has all denominator prime factors <=w whenever the fixed clearing denominator D<=w and the varying step m is w-smooth.',
    'RoughInterpolationIntegerValues proves the actual cleared polynomial at every integer point lies in the D denominator lattice. Closeness less than 1/D gives exact integer equality. With PowerDominates one eventual threshold works for all varying polynomials, smooth steps, and integer positions, and yields integral quotient values after the proved exact factorization.',
    'RoughInterpolationValueError combines interpolation error with distance to an integer and proves that dividing the error C*(S/Z)^e by a progression power t^e with t>=S>0 gives error <=C*Z^(-e), preserving the same constant C without progression-length dependence.'
]
remaining = (
    'StrongConjecture remains unproved; no unavoidable obstruction is established. Original exposed array joint '
    'coefficient-log polynomiality is proved. Section 06 interpolation now has exact rational lattices, derivative '
    'denominators, exact factorization and quotient degree, uniform growth thresholds, node-only common denominators, '
    'proved smooth quotient coefficient denominators, eventual integer quotient values and the final divided error '
    'scale. Still construct separated integer nodes and the actual Lagrange interpolant with error and derivative '
    'bounds independent of H, derive its degree and clearing certificates, and assemble the full interpolation lemma. '
    'Then prove corrected quantitative Leibman/box comparison and stretched-filtration prerequisites, smooth-progression '
    'dimension induction and uniform rough-step comparison over coefficients, boxes/endpoints, residues and tests. '
    'Package finite native readings and connect conditional face laws. Buffered short-bin geometry, prior-event positive '
    'probability, extra-conditioning posterior control, quantitative native smooth-observable bounds, conditional face '
    'invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and '
    'HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Complete final ordered positive rapidly '
    'separated monochromatic extraction. No independent kernel replay, external review, public contribution or prize '
    'submission is claimed.'
)
reviews = [
    'Checked pinned 06_rough_progressions exact interpolation proof, especially the denominator claim after division. It is now derived by actual monic quotient inside a subring, then multiplication by an allowed inverse; no prime support hypothesis is imposed on the quotient.',
    'The denominator subring is defined by explicit integer clearing certificates, with its ring laws proved. The separate denominator theorem shows the canonical reduced denominator divides a power of W, so membership implies the literal prime-factor condition used in the paper.',
    'The varying m is only assumed w-smooth and nonzero, not bounded by w. The theorem derives m dividing W^m from prime support. Only the fixed interpolation denominator D is absorbed using D<=w, consistent with fixing H before the asymptotic limit.',
    'The eventual integer-value threshold is chosen before all varying polynomials, t, m and sample positions. Polynomial clearing, actual factorization and numerical closeness remain explicit inputs to be supplied by the full interpolation construction. Roughness is on the actual affine progression value tau=t+m*z.',
    'Error division retains the same constant and thus cannot introduce an H dependence. It does not prove that the initial Lagrange constant is H-independent. That analytic estimate and construction of separated nodes remain unproved.',
    'A slow failed elaboration was stopped and diagnosed; only the final warning-free focused checks and full build are admitted as verification. All retained proof sources and axiom sets are unchanged. These are author-side checks, not independent kernel replay.'
]
replacements = dict(PREFIX='round-rough-smooth-quotient', OLD='round-rough-exact-division',
    MODULES=['Hindman168/'+m+'.lean' for m in modules], COMPONENTS=components, REMAINING=remaining)
lines = source.splitlines(keepends=True)
for node in reversed(ast.parse(source).body):
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno] = [name+' = '+repr(replacements[name])+'\n']
source = ''.join(lines).replace('Audit rough interpolation rational exactness and polynomial division.',
    'Audit smooth quotient denominators and integral interpolation values.')
source = re.sub(r'application_review=COMPONENTS\+\[.*?\]\+\[REMAINING\],',
    lambda _: 'application_review=COMPONENTS+'+repr(reviews)+'+[REMAINING],', source)
source = source.replace('06_rough_progressions lines 168-269: exact division after interpolation',
    '06_rough_progressions lines 232-269: smooth quotient and integer interpolation values')
Path('round-rough-smooth-quotient-audit.py').write_text(source, encoding='utf-8')
