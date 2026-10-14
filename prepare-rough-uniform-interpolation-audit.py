from pathlib import Path
import ast
import re

source = Path('round-rough-smooth-quotient-audit.py').read_text(encoding='utf-8')
modules = ['RoughInterpolationNodes', 'RoughPolynomialCoefficientBound', 'RoughFixedInterpolationBound',
    'RoughScaledInterpolation', 'RoughInterpolationUniformError', 'RoughRationalInterpolation',
    'RoughRationalInterpolationError']
components = [
    'RoughInterpolationNodes constructs h=floor((H-1)/q) and integer nodes j*h for j=0..q. Under q>0,H>=2q+2 it proves positivity, interval inclusion, injectivity, separation >=(H-1)/(2q), and the rescaled interval inclusion in [0,2q].',
    'RoughPolynomialCoefficientBound constructs the actual absolute coefficient sum and proves |P(x)|<=mass(P)*B^q for degree<=q, B>=1 and |x|<=B.',
    'RoughFixedInterpolationBound defines the fixed Lagrange bases at 0..q and a positive constant from all their derivatives through order q. It proves a uniform evaluation bound for derivatives of interpolants of eps-bounded data using only q and a spatial bound B.',
    'RoughScaledInterpolation constructs interpolation at j*h by composing the fixed-node interpolant with X/h. It proves degree<=q, exact node values, reproduction of every degree<=q polynomial, subtraction linearity, the iterated derivative scaling identity, and uniform derivative bounds for every h>=1.',
    'RoughInterpolationUniformError defines Cq from the fixed derivative coefficient mass and (1+2q)^q. It proves the original interval value error <=Cq*eps and external derivative error <=Cq*eps*(1+2S)^q for |a|<=2S, uniformly in H, coefficients and data. No H-dependent analytic constant is introduced.',
    'RoughRationalInterpolation constructs the actual rational Lagrange interpolant of integer data on the separated integer nodes. Its exact node values, degree<=q, map-to-real identity with the scaled interpolant, and positive clearing denominator fixed BEFORE all integer data are proved. The integer clearing polynomial also has degree<=q.',
    'RoughRationalInterpolationError transfers both uniform value and derivative error bounds to evaluations of the actual rational interpolant. The derivative bound uses casts of the actual rational iterated derivative, matching the earlier exact-division lattice theorem.'
]
remaining = (
    'StrongConjecture remains unproved; no unavoidable obstruction is established. Original exposed array joint '
    'coefficient-log polynomiality is proved. Section 06 interpolation now has separated integer nodes, actual rational '
    'interpolants with fixed node-only denominators and degree certificates, H-independent value and derivative error '
    'bounds, exact derivative lattices and division, smooth quotient denominators, eventual integer quotient values and '
    'the final divided error scale. Assemble the full interpolation lemma: choose integer data from its all-index '
    'approximation hypothesis, instantiate T=(t0+mX)^e*theta, prove low derivatives of T vanish at -t0/m and derive '
    '|t0/m|<=2S and m<=S from the progression geometry, then combine the existing uniform thresholds and conclusions. '
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
    'Checked 06_rough_progressions interpolation proof. Regularly spaced integer nodes j*floor((H-1)/q) are an allowed choice: every node and the required separation bound are proved. q>0 is explicit, as follows from q>=e>=1 in the paper.',
    'Cq is explicitly defined using finitely many fixed real Lagrange basis coefficient sums and derivatives. It depends on q alone. Scaled derivative factors h^(-j) are bounded by one using h>=1; this gives the paper-required coarse external derivative bound without needing a sharper H^(-j) estimate.',
    'The error polynomial identity is exact by polynomial reproduction and interpolation linearity, so the estimates depend on node errors rather than magnitudes of target polynomial coefficients or integer data.',
    'The rational model is the actual Lagrange interpolation at the integer nodes, not an assumed rational approximation. It maps exactly to the real scaled interpolation. A single D is selected before all integer values, and injectivity of the integer-to-rational map proves the numerator degree bound.',
    'The finite-node decidable equality mismatch was resolved by the proved subsingleton equality of the two decision functions; no new global instance or untrusted evaluation was introduced. An elaboration timeout was resolved by explicit sum indices and functions, without raising heartbeat limits.',
    'The full interpolation lemma still needs assembly with the actual progression and real polynomial T=(t0+mX)^e*theta. These verified components do not imply quantitative Leibman, rough-step comparison, or StrongConjecture.',
    'All retained proof sources and axiom sets are unchanged; these are author-side checks, not independent kernel replay.'
]
replacements = dict(PREFIX='round-rough-uniform-interpolation', OLD='round-rough-smooth-quotient',
    MODULES=['Hindman168/'+m+'.lean' for m in modules], COMPONENTS=components, REMAINING=remaining)
lines = source.splitlines(keepends=True)
for node in reversed(ast.parse(source).body):
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno] = [name+' = '+repr(replacements[name])+'\n']
source = ''.join(lines).replace('Audit smooth quotient denominators and integral interpolation values.',
    'Audit separated-node rational interpolation and length-independent analytic bounds.')
source = re.sub(r'application_review=COMPONENTS\+\[.*?\]\+\[REMAINING\],',
    lambda _: 'application_review=COMPONENTS+'+repr(reviews)+'+[REMAINING],', source)
source = source.replace('06_rough_progressions lines 232-269: smooth quotient and integer interpolation values',
    '06_rough_progressions lines 168-243: separated nodes and uniform interpolation bounds')
Path('round-rough-uniform-interpolation-audit.py').write_text(source, encoding='utf-8')
