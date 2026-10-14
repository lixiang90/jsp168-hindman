from pathlib import Path
import ast
import re

source = Path('round-canonical-face-counting-audit.py').read_text(encoding='utf-8')
components = [
    'FiniteVectorPolynomialDegree defines an exponent-support upper bound for the actual finite coefficient lists. It proves monotonicity, singleton, append, finite sum, rational scaling, primitive, bilinear composition and iterated adjoint-power bounds. Zero coefficients and cancellation need no assumptions.',
    'NativeLiePolynomialDegree propagates these bounds through the actual native dexp defect, defect powers, logarithm vector field and Picard recursion. For nilpotency class C, Picard iteration n has exponent bound (C*C+1)^n and the actual native product-log polynomial has bound (C*C+1)^(C+1). No coefficient bounds or formal BCH model are used.',
    'NativeLieOrbitLogPolynomial constructs an explicit polynomial list for the actual native global logarithm of g^k*x for every signed integer k, using Log(x), Log(x^-1*g*x) and the original product-log curve. Its degree is uniformly at most (s*s+1)^(s+1) whenever the actual group nilpotency class is at most s.'
]
remaining = (
    'StrongConjecture remains unproved; no unavoidable obstruction is established. A uniform-degree actual native '
    'integer-orbit logarithm polynomial is now proved. Compose this polynomial with the exposed multivariate scalar '
    'exponent at the finitely many array evaluation points, then apply the proved linear coefficient recovery to obtain '
    'joint native array-log polynomiality with uniform degree after actual tail substitutions. The current orbit theorem '
    'alone does not establish that joint statement. Connect the native face observable identity and sampling estimates '
    'to conditional marginal cube laws. Prove and apply the uniform rough-step proposition of section 06, including '
    'coefficients, endpoints, residues and tests. Buffered short-bin geometry, prior-event positive probability, posterior '
    'control after additional prior conditioning, quantitative native smooth-observable bounds, conditional face invariance '
    'and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence '
    'remain explicit unproved existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. '
    'Standard-only axiom reports do not prove the full target. No independent kernel replay, external review, public '
    'contribution or prize submission is claimed.'
)
reviews = [
    'The degree predicate bounds every exponent in the existing list representation. It is a sufficient polynomial degree bound, not a claim of minimal degree; cancellations and zero coefficients cannot invalidate it.',
    'The defect bound C*d+e and field bound C*(C*d)+e follow from their actual finite ranges. Picard starts at a constant and appends a primitive, so (C*C+1)^n is a valid coarse recursive bound even for C=0.',
    'The integer-time one-parameter identity is derived from the actual additive homomorphism via map_zsmul. The orbit identity uses g^k*x=x*(x^-1*g*x)^k and native exponential/global-log inverse identities. No commutativity or replacement group is assumed.',
    'The bound (s*s+1)^(s+1) is uniform over g, x and all coefficient values for every group with nilpotencyClass<=s. The logarithm evaluation requires the existing complete finite-dimensional simply connected nilpotent native Lie-group hypotheses explicitly.',
    'Checked the joint-log-polynomiality obligation in pinned 08_alignment lines 498-509. This is the actual orbit ingredient with degree control. Multivariate composition, array coordinate recovery and substitution of individual tail factors remain to be proved; the rough-step theorem is not inferred from univariate polynomiality.',
    'Retained sources and axiom sets are unchanged. Verification is author-side, with no independent kernel replay or claim of full StrongConjecture.'
]
replacements = dict(PREFIX='round-native-orbit-degree', OLD='round-canonical-face-counting',
    MODULES=['Hindman168/'+m+'.lean' for m in ['FiniteVectorPolynomialDegree',
        'NativeLiePolynomialDegree', 'NativeLieOrbitLogPolynomial']], COMPONENTS=components, REMAINING=remaining)
lines = source.splitlines(keepends=True)
for node in reversed(ast.parse(source).body):
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno] = [name+' = '+repr(replacements[name])+'\n']
source = ''.join(lines).replace('Audit actual canonical Delta divisibility, scale growth and uniform face counting.',
    'Audit uniform exponent bounds and the actual native integer-orbit log polynomial.')
source = re.sub(r'application_review=COMPONENTS\+\[.*?\]\+\[REMAINING\],',
    lambda _: 'application_review=COMPONENTS+'+repr(reviews)+'+[REMAINING],', source)
source = source.replace('08_alignment lines 550-567: actual canonical face-shift counting',
    '08_alignment lines 498-509: uniform-degree joint logarithm polynomiality ingredient')
Path('round-native-orbit-degree-audit.py').write_text(source, encoding='utf-8')
