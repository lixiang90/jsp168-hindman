from pathlib import Path
import ast
import re

source = Path('round-retained-box-geometry-audit.py').read_text(encoding='utf-8')
components = [
    'FiniteComplexMassMean defines the actual finite complex expectation, proves its sum/subtraction formulas and its bounded-test L1 comparison, and identifies uniform finite mass expectation with the literal normalized set mean including empty sets. A sign witness and the existing set-mean symmetric-difference bound give an unequal-size uniform law L1 estimate requiring only source nonempty.',
    'UniformBoxMassComparison proves exact equality of the uniform law on an arbitrary finite product box and the product of coordinate uniform laws. For nonempty source and target coordinate sets it applies the existing probability product L1 theorem to obtain the sum of coordinate symmetric-difference errors, also for arbitrary bounded complex tests.',
    'AlignmentBoxEndpointError gives the multidimensional forward endpoint perturbation estimate sum_j 4*K*D/(U_j-L_j). Canonical residue endpoint alignment is specialized with side >=2*d, which proves both original and target coordinate sets nonempty.',
    'AlignmentActualBoxEndpointError absorbs the full sum at the actual step d*tail_product. For every fixed finite dimension, c>0, K>=0 and epsilon>0, one threshold works for all positive tail samples, all integer endpoints with side >=c*Z, all residues and all globally K-bounded complex tests. Endpoint-aligned unrestricted product means differ by at most epsilon.'
]
remaining = (
    'StrongConjecture remains unproved; no unavoidable obstruction is established. Permitted original box geometry, '
    'retained-step geometry and full exact normalized mean transport are proved. Multidimensional forward endpoint '
    'perturbation and actual full-step residue endpoint alignment errors are now proved uniformly for bounded complex tests. '
    'These compare unrestricted means before and after endpoint alignment; they do not equate sparse residue sampling with '
    'unrestricted sampling. Prove the required signed face-translation estimates and connect sampling results to actual '
    'conditional marginal cube laws. Prove uniform-degree joint native logarithm polynomiality after substituting the '
    'exposed scalar exponent and tail product. Prove and apply the uniform rough-step proposition of section 06, including '
    'coefficients, endpoints, residues and tests. Buffered short-bin geometry, prior-event positive probability, posterior '
    'control after additional prior conditioning, quantitative native smooth-observable bounds, conditional face invariance '
    'and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence '
    'remain explicit unproved existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. '
    'Standard-only axiom reports do not prove the full target. No independent kernel replay, external review, public '
    'contribution or prize submission is claimed.'
)
reviews = [
    'The product law identity is exact, including empty coordinate sets and zero-dimensional products. The product L1 inequality is used only after explicitly proving every coordinate law has total mass one.',
    'The unequal-cardinality distance estimate uses a bounded sign witness; it does not silently identify different normalizing denominators. The complex expectation bridge uses the original normalized finite sum exactly.',
    'Forward endpoint moves are allowed independently at both ends with displacement at most D. In the residue-alignment specialization, side >=2*d proves target nonemptiness from the strict endpoint displacement <d.',
    'Actual uniformity includes samples, endpoints, residues and tests. The auxiliary eta=epsilon/(card+1) handles zero-dimensional index types; K+1 handles K=0 without division by zero. The threshold combines side preservation and total-error smallness.',
    'Checked pinned 08_alignment lines 488-495 and 550-567. The current statements prove the endpoint counting cost for unrestricted boxes. Residue restrictions are preserved exactly by earlier alignment identities, while removing their factors still requires the unproved rough-step input. General signed face translations are not claimed here.',
    'Generic difference-set lemmas carry explicit DecidableEq arguments so their integer specializations use the same set operations. No local instance workaround, new axiom, weakened target or altered prior proof is introduced.'
]
replacements = dict(PREFIX='round-box-endpoint-error', OLD='round-retained-box-geometry',
    MODULES=['Hindman168/'+m+'.lean' for m in ['FiniteComplexMassMean', 'UniformBoxMassComparison',
        'AlignmentBoxEndpointError', 'AlignmentActualBoxEndpointError']],
    COMPONENTS=components, REMAINING=remaining)
lines = source.splitlines(keepends=True)
for node in reversed(ast.parse(source).body):
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno] = [name+' = '+repr(replacements[name])+'\n']
source = ''.join(lines).replace('Audit exact retained-step endpoint division and uniform normalized box geometry.',
    'Audit actual multidimensional endpoint errors and exact uniform product laws.')
source = re.sub(r'application_review=COMPONENTS\+\[.*?\]\+\[REMAINING\],',
    lambda _: 'application_review=COMPONENTS+'+repr(reviews)+'+[REMAINING],', source)
source = source.replace('08_alignment lines 392-417 and 511-542: all permitted boxes after retained-step division',
    '08_alignment lines 488-495 and 550-567: normalized box endpoint counting costs')
Path('round-box-endpoint-error-audit.py').write_text(source, encoding='utf-8')
