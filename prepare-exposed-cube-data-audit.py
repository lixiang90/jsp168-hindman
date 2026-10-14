from pathlib import Path
import ast
import json
import re

path = Path('round-retained-crt-audit.py')
source = path.read_text(encoding='utf-8')
modules = ['AlignmentDyadicResidueGrowth', 'AlignmentDyadicResidueLimit',
           'AlignmentFrozenCubeData', 'AlignmentExposedCubePolynomial',
           'AlignmentExposedCubeEvaluation']
components = [
    'The previously unregistered dyadic residue growth draft is checked and registered. Actual exposure modulus L=M*W^w is bounded by the square of the auxiliary scale; actual cutoff growth proves S/L tends to infinity uniformly over all finite tail indices and all cutoff-supported values, including arbitrary varying sequences.',
    'Actual short-exposure equality fixes short-bin width and origin, hence the integer basepoint Y=floor(Q/M), and fixes every pivot array residue for any pivot in the exposed residue class. After fixing retained factor values and a chosen d residue, the literal bounded retained CRT representative is fixed across the complete exposure fiber.',
    'A canonical rational scalar exponent polynomial is constructed from actual exposed data, has total degree at most two, and is proved identical across the complete exposure fiber. Own-target numerator filtering is retained, with no claim that other numerators are fixed.',
    'The exposed polynomial evaluates exactly to the original numerical array integer quotient for every cube vertex, any integer origin in the exposed pivot residue class, and arbitrary integer array indices. The unexposed pivot microcell enters only the vertex coordinate. This remains a scalar exponent statement, not the required native joint BCH log-polynomiality.'
]
remaining = (
    'StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'Completed arithmetic connections now include uniform dyadic S/L divergence, actual retained-scale power domination, '
    'retained CRT representatives fixed under the complete exposure and fixed retained factors, and a single exposure-fixed '
    'degree-two scalar exponent polynomial with exact evaluation at original numerical cube arguments. '
    'Construct concrete permitted cube boxes and prove original side lower bounds; connect residue sample-set transport to '
    'normalized finite averages and uniform counting/endpoint losses. Prove joint polynomiality in the native array Lie algebra '
    'by BCH after substituting the actual tail product; the scalar exponent result does not supply this. '
    'Prove and apply the uniform rough-step proposition of section 06, including uniformity in coefficients, endpoints, '
    'residue vectors and tests. Buffered short-bin geometry, prior-event positive probability and posterior control after '
    'additional prior conditioning, quantitative smooth-observable bounds, conditional face invariance and positive-probability '
    'Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved '
    'existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. '
    'Existing conditional theorems and standard-only axiom reports are not a full proof. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.'
)
replacements = dict(PREFIX='round-exposed-cube-data', OLD='round-retained-crt',
    MODULES=['Hindman168/'+m+'.lean' for m in modules], COMPONENTS=components, REMAINING=remaining)
tree = ast.parse(source)
lines = source.splitlines(keepends=True)
for node in reversed(tree.body):
    if isinstance(node, ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0], ast.Name):
        name=node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno] = [name+' = '+repr(replacements[name])+'\n']
source=''.join(lines)
source=source.replace('Audit explicit actual retained CRT representatives and update invariance.',
    'Audit actual exposed cube data, scalar polynomial evaluation and dyadic scale divergence.')
reviews = [
    'Reviewed quantifier order: one threshold works for all finite indices and all cutoff-supported values. The growth proof covers varying sample and index sequences.',
    'Reviewed exposure scope: retained factor equality is an additional conditioning hypothesis, while Y and r follow from the actual short exposure. No exact pivot microcell or independence after short-bin conditioning is assumed.',
    'Exact evaluation caught and repaired an integer-division coercion in the new polynomial definition: Y is explicitly an integer quotient before rational embedding. The original numerical quotient is checked without a divisibility shortcut.',
    'Reviewed own-target filtering and degree scope: non-own numerators may vary, and neither joint native BCH polynomiality nor the uniform rough-step conclusion is asserted.',
    'All retained proof source hashes and prior transitive axiom sets are unchanged. No independent kernel replay or full-target proof is claimed.'
]
source=re.sub(r'application_review=COMPONENTS\+\[.*?\]\+\[REMAINING\],',
    lambda _: 'application_review=COMPONENTS+'+repr(reviews)+'+[REMAINING],', source)
source=source.replace('08_alignment: retained CRT representatives independent of the removed factor',
    '08_alignment lines 425-550: complete exposed cube data and dyadic scale divergence')
source=source.replace("    fixed = obj(OLD+'-preprint-local-check.json')\n",
    "    fixed = obj(OLD+'-preprint-local-check.json')\n"
    "    rough = obj('round-cube-coordinates-rough-step-reference.json')\n"
    "    assert rough['commit'] == fixed['fixed_openai_math_commit']\n"
    "    fixed['sections'].append(dict(path=rough['path'], normalized_sha256=rough['normalized_sha256'],\n"
    "        matches_pinned_git_object=True))\n")
Path('round-exposed-cube-data-audit.py').write_text(source,encoding='utf-8')
