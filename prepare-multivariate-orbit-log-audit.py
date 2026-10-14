from pathlib import Path
import ast
import re

source = Path('round-native-orbit-degree-audit.py').read_text(encoding='utf-8')
components = [
    'VectorPolynomialMultivariateProjection constructs the explicit real multivariate polynomial sum C(ell(v))*P^m from each actual finite vector polynomial list. Evaluation equals ell of the original vector polynomial evaluated at P, and total degree is bounded by the list exponent bound times totalDegree(P).',
    'NativeLieMultivariateOrbitLog composes the actual native orbit-log polynomial with any real multivariate scalar polynomial. It proves degree <=(s*s+1)^(s+1)*d and exact evaluation of ell(Log(g^k*x)) wherever the scalar polynomial equals the signed integer k.',
    'RationalPolynomialRealTransfer proves degree nonincrease and exact evaluation compatibility under the actual coefficient map from Q to R.',
    'AlignmentExposedOrbitLogPolynomial applies the composition to the original exposure-fixed scalar exponent. Each projected log polynomial has total degree <=2*(s*s+1)^(s+1), exact integer-orbit evaluation, and equality on the original complete exposure fiber when the group data and linear coordinate are fixed.',
    'AlignmentActualOrbitLogEvaluation discharges scalar-integrality and evaluation premises using the proved original canonical cube exponent identity. At the actual cube vertex and tail product, the projected polynomial equals the true native log of g raised to the original integer array quotient, multiplied by the fixed orbit origin.'
]
remaining = (
    'StrongConjecture remains unproved; no unavoidable obstruction is established. Explicit bounded-degree real '
    'multivariate polynomials now represent every linear projection of the actual orbit logarithm after the original '
    'exposure-fixed scalar exponent, with exact evaluation at admissible original cube samples. Recover the native array '
    'logarithm via the fixed finite evaluation image and linear coefficient recovery/retraction; then substitute cube '
    'vertex and individual tail variables with a uniform degree bound. The present projected orbit statement does not '
    'yet prove the full array-group joint-log-polynomial theorem. Connect native face observables and counting estimates '
    'to conditional marginal cube laws. Prove and apply uniform rough-step section 06, including coefficients, endpoints, '
    'residues and tests. Buffered short-bin geometry, prior-event positive probability, extra-conditioning posterior '
    'control, quantitative native smooth-observable bounds, conditional face invariance and positive-probability Alignment '
    'remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence '
    'inputs. Complete final ordered positive rapidly separated monochromatic extraction. Standard-only axiom reports do '
    'not prove the full target. No independent kernel replay, external review, public contribution or prize submission is claimed.'
)
reviews = [
    'Composition is explicit in MvPolynomial over R and uses an arbitrary actual real linear functional. Its degree proof uses totalDegree_add, multiplication and powers; coefficient size is unrestricted.',
    'Q-to-R transfer is the actual Rat.castHom coefficient map. Support inclusion proves degree nonincrease, and ring evaluation commutation proves the value identity. The integer cast is preserved exactly.',
    'The exposed polynomial keeps unknown microcell origin in X, the variable coordinate. Equality on the exposure fiber uses the prior frozen scalar polynomial theorem; g, orbit origin and linear coordinate are fixed parameters, not newly proved frozen data.',
    'The actual evaluation theorem invokes alignmentExposedCubePolynomial_eval directly and uses the original integer division by M. It imposes no independent integrality assumption and includes signed vertices and array indices.',
    'Checked pinned 08_alignment lines 498-509: projected single-orbit polynomiality is now proved after the literal exponent. The finite evaluation retraction and native array-log identification, followed by substitution of separate tail factors, remain pending. No rough-step or full joint-array conclusion is claimed.',
    'All retained sources and axiom sets are unchanged; verification is author-side rather than independent kernel replay.'
]
replacements = dict(PREFIX='round-multivariate-orbit-log', OLD='round-native-orbit-degree',
    MODULES=['Hindman168/'+m+'.lean' for m in ['VectorPolynomialMultivariateProjection',
        'NativeLieMultivariateOrbitLog', 'RationalPolynomialRealTransfer',
        'AlignmentExposedOrbitLogPolynomial', 'AlignmentActualOrbitLogEvaluation']],
    COMPONENTS=components, REMAINING=remaining)
lines = source.splitlines(keepends=True)
for node in reversed(ast.parse(source).body):
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno] = [name+' = '+repr(replacements[name])+'\n']
source = ''.join(lines).replace('Audit uniform exponent bounds and the actual native integer-orbit log polynomial.',
    'Audit explicit multivariate native orbit-log projection and original cube evaluation.')
source = re.sub(r'application_review=COMPONENTS\+\[.*?\]\+\[REMAINING\],',
    lambda _: 'application_review=COMPONENTS+'+repr(reviews)+'+[REMAINING],', source)
source = source.replace('08_alignment lines 498-509: uniform-degree joint logarithm polynomiality ingredient',
    '08_alignment lines 498-509: multivariate native log coordinates after the original exponent')
Path('round-multivariate-orbit-log-audit.py').write_text(source, encoding='utf-8')
