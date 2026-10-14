from pathlib import Path
import ast
import re

source = Path('round-box-endpoint-error-audit.py').read_text(encoding='utf-8')
components = [
    'ComplexMassTranslation proves exact complex expectation pushforward and a bounded complex-test translation estimate for the actual independent coordinate law using the existing product L1 bound.',
    'ComplexBoxTranslation identifies arbitrary signed-endpoint integer intervals with the original uniformIntervalMass and proves full-box signed translation error <=K*sum_j 2*abs(u_j)/(U_j-L_j), for all nonempty coordinate intervals and bounded complex tests.',
    'AlignmentResidueBoxTranslation proves exact normalized division of every residue box by its positive step, then derives signed translations divisible by that step with error <=K*sum_j 4*abs(u_j)/(U_j-L_j), provided each side is at least twice the step. The common-scale version bounds this by 4*K*sum_j abs(u_j)/(c*Z).'
]
remaining = (
    'StrongConjecture remains unproved; no unavoidable obstruction is established. Permitted original and retained-step '
    'box geometry, exact normalized transport, multidimensional endpoint errors and signed residue-preserving box '
    'translation estimates are proved. Instantiate translation estimates with actual own-pair shifts, proving their '
    'uniform divisibility and smallness relative to Z, and connect sampling results to actual conditional marginal cube '
    'laws. Prove uniform-degree joint native logarithm polynomiality after substituting exposed exponents and tail factors. '
    'Prove and apply the uniform rough-step proposition of section 06, including coefficients, endpoints, residues and '
    'tests. Buffered short-bin geometry, prior-event positive probability, posterior control after additional prior '
    'conditioning, quantitative native smooth-observable bounds, conditional face invariance and positive-probability '
    'Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved '
    'existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. Standard-only axiom '
    'reports do not prove the full target. No independent kernel replay, external review, public contribution or prize '
    'submission is claimed.'
)
reviews = [
    'All translations are signed integers; no positivity hypothesis on displacement is introduced. Complex pushforward is exact for arbitrary maps, not only injective ones.',
    'The residue-restricted estimate retains the original r mod d class and explicitly requires d divides every shift. It makes no comparison between sparse residue sampling and unrestricted sampling.',
    'Integer retained endpoints use exact congruence alignment; arbitrary signed representatives are allowed. Side error <d and original side>=2*d prove divided interval positivity and at least half the original scaled length. No bounded representative is needed for side comparisons.',
    'The resulting scale estimate is O(sum abs(u)/Z) under side>=2*d. This is sufficient for the paper face-translation counting term once actual shift smallness is supplied, but that actual parameter application is still pending.',
    'Checked against pinned 08_alignment lines 550-567: face invariance additionally requires rough-step removal, actual Delta divisibility and growth, and the native observable identity. None of these is inferred from the geometric translation theorem.',
    'Prior proof files and axiom sets are retained. This is author-side verification, not independent kernel replay or a complete proof of StrongConjecture.'
]
replacements = dict(PREFIX='round-box-translation', OLD='round-box-endpoint-error',
    MODULES=['Hindman168/'+m+'.lean' for m in ['ComplexMassTranslation', 'ComplexBoxTranslation',
        'AlignmentResidueBoxTranslation']], COMPONENTS=components, REMAINING=remaining)
lines = source.splitlines(keepends=True)
for node in reversed(ast.parse(source).body):
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno] = [name+' = '+repr(replacements[name])+'\n']
source = ''.join(lines).replace('Audit actual multidimensional endpoint errors and exact uniform product laws.',
    'Audit signed complex box translations preserving residue restrictions.')
source = re.sub(r'application_review=COMPONENTS\+\[.*?\]\+\[REMAINING\],',
    lambda _: 'application_review=COMPONENTS+'+repr(reviews)+'+[REMAINING],', source)
source = source.replace('08_alignment lines 488-495 and 550-567: normalized box endpoint counting costs',
    '08_alignment lines 550-567: signed residue-preserving face translations')
Path('round-box-translation-audit.py').write_text(source, encoding='utf-8')
