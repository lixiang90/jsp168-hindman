from pathlib import Path
import ast
import re

source = Path('round-exposed-joint-log-audit.py').read_text(encoding='utf-8')
modules = ['RoughRationalExactness', 'RoughPolynomialDenominators',
    'RoughPolynomialExactDivision', 'RoughInterpolationExactnessScale', 'RoughInterpolationDenominator']
components = [
    'RoughRationalExactness proves exact zero and exact nearest-integer identities for real numbers in a specified denominator lattice. Bezout gives integer cancellation for a rational value whose two coprime integer multiples are integral; actual primorial-smooth denominator and rough power specialization is proved.',
    'RoughPolynomialDenominators uses genuine integer polynomials to clear evaluation denominators at a/m, with a uniform m^q bound for every iterated derivative. A certificate C(D)*R=map(P) and natDegree(P)<=q yield a D*m^q lattice certificate. The real strict gap bound forces exact rational derivative vanishing.',
    'RoughPolynomialExactDivision turns vanishing low-order derivatives into the exact factor (t+mX)^e over Q, including zero polynomial and e=0 cases, and proves quotient degree <=q-e. Combining with denominator lattices proves exact division from strict derivative error bounds, without assuming divisibility.',
    'RoughInterpolationExactnessScale derives C*(S/Z)^e*(1+2S)^q <1/(D*S^q) from actual PowerDominates and eventual S>=1,Z>=0. For fixed D,q,e,C one eventual threshold works for all varying polynomials, t and positive m<=S with the stated clearing certificate and derivative estimate, and yields exact division.',
    'RoughInterpolationDenominator proves that a fixed finite family of rational polynomials admits one positive natural clearing denominator. Applying this to the fixed rational Lagrange bases yields a denominator depending only on the chosen integer nodes, uniformly over ALL integer interpolation values. The construction uses actual integer normalization and a finite product, not a denominator-size assumption.'
]
remaining = (
    'StrongConjecture remains unproved; no unavoidable obstruction is established. Original exposed array joint '
    'coefficient-log polynomiality is proved. Section 06 interpolation now has exact rational lattice, derivative '
    'denominator, root multiplicity, factorization, quotient degree, growth-threshold and node-only common denominator '
    'components. Still construct the actual separated nodes and interpolant error with constants independent of H, '
    'derive its derivative estimates and actual degree certificates, prove quotient coefficient denominators remain '
    'smooth under division, and connect exact integer evaluation and the final interpolation error. Then prove corrected '
    'quantitative Leibman/box comparison and stretched filtration prerequisites, smooth-progression dimension induction '
    'and uniform rough-step comparison, uniformly over coefficients, boxes/endpoints, residues and tests. Package finite '
    'native readings and connect conditional face laws. Buffered short-bin geometry, prior-event positive probability, '
    'extra-conditioning posterior control, quantitative native smooth-observable bounds, conditional face invariance '
    'and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence '
    'remain explicit unproved existence inputs. Complete final ordered positive rapidly separated monochromatic '
    'extraction. No independent kernel replay, external review, public contribution or prize submission is claimed.'
)
reviews = [
    'Checked pinned 06_rough_progressions interpolation proof: rational exactness uses the fixed node denominator D_H and m^q. The derivative denominator bound is proved for every derivative index through integer polynomial differentiation and denominator clearing, rather than assumed for sampled rational values.',
    'The eventual exactness threshold is quantified before all polynomials, t and m at that index. D and the derivative majorant constant must be fixed before the limit; the fixed denominator theorem supplies the required independence of integer data once nodes are fixed. Thresholds may depend on the progression length through its nodes.',
    'Strict inequalities, positive D and m, zero polynomials, e=0 in the algebraic theorem, and positive e in the scale theorem are handled explicitly. Quotient degree uses root multiplicity and exact polynomial multiplication. No derivative-root multiplicity is assumed.',
    'The arithmetic cancellation uses two integral multiples with coprime multipliers, so it proves the intended reduced-denominator conclusion without an unnecessary lowest-terms hypothesis. Applying it to the eventual quotient still requires proving smoothness of its coefficient denominators.',
    'Derivative majorants and separated-node interpolation estimates are still explicit remaining work. These theorems do not prove the full interpolation lemma, quantitative equidistribution, rough-step comparison, or StrongConjecture. No H-dependent analytic constant has been presented as H-independent.',
    'All retained proof sources and axiom sets are unchanged; this is author-side checking, not independent kernel replay.'
]
replacements = dict(PREFIX='round-rough-exact-division', OLD='round-exposed-joint-log',
    MODULES=['Hindman168/'+m+'.lean' for m in modules], COMPONENTS=components, REMAINING=remaining)
lines = source.splitlines(keepends=True)
for node in reversed(ast.parse(source).body):
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno] = [name+' = '+repr(replacements[name])+'\n']
source = ''.join(lines).replace('Audit original frozen cube array logarithms jointly in cube and tail variables.',
    'Audit rough interpolation rational exactness and polynomial division.')
source = re.sub(r'application_review=COMPONENTS\+\[.*?\]\+\[REMAINING\],',
    lambda _: 'application_review=COMPONENTS+'+repr(reviews)+'+[REMAINING],', source)
source = source.replace('08_alignment lines 496-509: original frozen cube array joint polynomiality',
    '06_rough_progressions lines 168-269: exact division after interpolation')
Path('round-rough-exact-division-audit.py').write_text(source, encoding='utf-8')
