from pathlib import Path
import ast
import re

source = Path('round-multivariate-orbit-log-audit.py').read_text(encoding='utf-8')
components = [
    'AlignmentNativeCoefficientLog constructs coefficient logarithms from the actual array exponential homeomorphism and its proved model-to-coefficient equivalence. Every integer evaluation is the actual original native global logarithm. It constructs a linear left inverse of the selected evaluation map on the whole ambient tuple space and proves exact recovery for all actual arrays.',
    'NativeFiniteOrbitLogProjection explicitly sums coordinate orbit-log polynomials for any real linear functional on a finite tuple. Its evaluation is the functional of the genuine coordinate logs, and its degree bound does not grow with the number of selected evaluation points.',
    'AlignmentNativeArrayLogPolynomial composes that tuple polynomial with the fixed selected-evaluation recovery map. It represents every linear coefficient-log coordinate of actual arrays with the prescribed selected integer-orbit values, with total degree <=(s*s+1)^(s+1)*d.',
    'AlignmentNativeModelLogPolynomial specializes recovery to the original alignmentNativeModelArray(g,b,k,Delta), constructing selected exponents P+sum C(u_j(e))*Q_e. If P and Q have degree<=d, the coefficient-log polynomial has degree <=(s*s+1)^(s+1)*d and equals the actual model-array coefficient logarithm at every admissible integer parameter point.'
]
remaining = (
    'StrongConjecture remains unproved; no unavoidable obstruction is established. Actual array coefficient logarithms '
    'are now recovered by a proved fixed linear map from selected native pointwise logs. Explicit bounded-degree '
    'polynomials for all linear coefficient-log coordinates of the original model array are proved for polynomial base '
    'and increment parameters. Instantiate those base/increment polynomials with original frozen cube data and substitute '
    'the vertex and separate tail-factor variables, proving the exact original model-array identity and uniform degree. '
    'Connect native face observables and counting to conditional marginal cube laws. Prove and apply uniform rough-step '
    'section 06, including coefficients, endpoints, residues and tests. Buffered short-bin geometry, prior-event positive '
    'probability, extra-conditioning posterior control, quantitative native smooth-observable bounds, conditional face '
    'invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and '
    'HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Complete final ordered positive rapidly '
    'separated monochromatic extraction. Standard-only axiom reports do not prove the full target. No independent kernel '
    'replay, external review, public contribution or prize submission is claimed.'
)
reviews = [
    'Coefficient logarithm is defined through the existing genuine array exponential homeomorphism and proved coefficient linear equivalence. Its evaluation equals native GlobalLog at EVERY integer slot by the actual Exp/Log inverse, not an assumed reconstruction law.',
    'Selected evaluation injectivity follows from the original finite native evaluation embedding and coordinate injectivity. LinearMap.leftInverse supplies a fixed global linear extension; it is proved a left inverse using the injectivity hypothesis. No image-membership premise is imposed on arbitrary real polynomial values.',
    'The finite tuple functional decomposes through LinearMap.single and the exact finite sum of coordinate inclusions. Finite summation preserves the common total-degree bound; the number and positions of evaluation points can affect coefficients but not degree.',
    'Actual model arrays are used via alignmentNativeModelArray, whose membership in the original array group was already proved. Their selected values are definitionally g^(k+sum u*Delta)*b. Polynomial evaluation hypotheses specify integer parameters, not polynomiality of the desired logarithm.',
    'Checked pinned 08_alignment lines 498-509: native array-log recovery is now proved. Substitution of frozen exposure data and individual tail factors is still required before claiming the entire original joint-polynomiality obligation. Rough-step uniformity and conditional face invariance remain open.',
    'All retained proof sources and axiom sets are unchanged; these are author-side checks, not independent kernel replay.'
]
replacements = dict(PREFIX='round-array-log-recovery', OLD='round-multivariate-orbit-log',
    MODULES=['Hindman168/'+m+'.lean' for m in ['AlignmentNativeCoefficientLog',
        'NativeFiniteOrbitLogProjection', 'AlignmentNativeArrayLogPolynomial', 'AlignmentNativeModelLogPolynomial']],
    COMPONENTS=components, REMAINING=remaining)
lines = source.splitlines(keepends=True)
for node in reversed(ast.parse(source).body):
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno] = [name+' = '+repr(replacements[name])+'\n']
source = ''.join(lines).replace('Audit explicit multivariate native orbit-log projection and original cube evaluation.',
    'Audit actual native array coefficient logarithms and polynomial linear recovery.')
source = re.sub(r'application_review=COMPONENTS\+\[.*?\]\+\[REMAINING\],',
    lambda _: 'application_review=COMPONENTS+'+repr(reviews)+'+[REMAINING],', source)
source = source.replace('08_alignment lines 498-509: multivariate native log coordinates after the original exponent',
    '08_alignment lines 498-509: native array logarithms recovered from finite evaluations')
Path('round-array-log-recovery-audit.py').write_text(source, encoding='utf-8')
