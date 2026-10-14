from pathlib import Path
import ast
import re

source = Path('round-box-translation-audit.py').read_text(encoding='utf-8')
components = [
    'AlignmentCanonicalShiftScale proves eventual fixed-modulus divisibility of the literal alignmentPairProgression, using alignmentPairResidue_master_data for the actual canonical representative. It proves abs(Delta)<=epsilon*Z uniformly over all rough tuples in earlier cutoffs and all adding pairs, by the proved abs(M*Delta)<=2*aux^3 and actual master width growth.',
    'AlignmentSingleCoordinateTranslation specializes the signed residue-preserving box estimate to a single coordinate, with bound 4*K*abs(Delta)/(c*Z), preserving arbitrary residue vectors and signed endpoints.',
    'AlignmentCanonicalFaceCounting combines canonical divisibility, uniform smallness and the actual positive scale into one eventual threshold for every tuple, pair, coordinate, side-bounded box, residue vector and bounded complex test. It proves translation error at most epsilon for the literal canonical Delta.',
    'AlignmentRawFaceCounting discharges roughness and earlier-cutoff hypotheses from original globalRawMass support. The actual canonical-coordinate translation estimate is consequently uniform over every supported sample and all permitted common-scale boxes.'
]
remaining = (
    'StrongConjecture remains unproved; no unavoidable obstruction is established. Actual canonical Delta divisibility, '
    'uniform smallness and single-coordinate residue-box counting errors are now proved, including original raw-supported '
    'samples. Connect the native face observable identity to these translated tests and the resulting sampling statements '
    'to conditional marginal cube laws. Prove uniform-degree joint native logarithm polynomiality after substituting exposed '
    'exponents and tail factors. Prove and apply the uniform rough-step proposition of section 06, including coefficients, '
    'endpoints, residues and tests. Buffered short-bin geometry, prior-event positive probability, posterior control after '
    'additional prior conditioning, quantitative native smooth-observable bounds, conditional face invariance and '
    'positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence '
    'remain explicit unproved existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. '
    'Standard-only axiom reports do not prove the full target. No independent kernel replay, external review, public '
    'contribution or prize submission is claimed.'
)
reviews = [
    'The shift is the existing alignmentPairProgression, not an existentially reselected displacement. Its canonical residue theorem already proves uniqueness and the full primorial-power divisibility; fixed d divisibility follows from that exact data.',
    'Uniform smallness uses the actual integer numerator and exact M*Delta identity. The modulus is positive, and the dyadic lower product is at least one, justifying division and transfer from R/M to Z. The threshold precedes all samples and adding pairs.',
    'The single-coordinate sum reduces exactly to abs(Delta). Fixed-d smallness is derived from retained scale growth with q=1, giving c*Z>=2*d>0 before using the counting estimate. K+1 avoids a division-by-zero case when K=0.',
    'Original raw support implies roughness and cutoff bounds through existing proved support geometry. No posterior independence, fixed endpoint, bounded residue representative, or unproved conditional regularity is introduced.',
    'Compared with pinned 08_alignment lines 550-567: this completes the actual shift counting part. It does not apply rough-step removal or identify the original native face action on the chosen observable; those remain explicit obligations.',
    'All retained proof sources and axiom sets are unchanged; these checks are author-side verification, not independent kernel replay.'
]
replacements = dict(PREFIX='round-canonical-face-counting', OLD='round-box-translation',
    MODULES=['Hindman168/'+m+'.lean' for m in ['AlignmentCanonicalShiftScale',
        'AlignmentSingleCoordinateTranslation', 'AlignmentCanonicalFaceCounting', 'AlignmentRawFaceCounting']],
    COMPONENTS=components, REMAINING=remaining)
lines = source.splitlines(keepends=True)
for node in reversed(ast.parse(source).body):
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno] = [name+' = '+repr(replacements[name])+'\n']
source = ''.join(lines).replace('Audit signed complex box translations preserving residue restrictions.',
    'Audit actual canonical Delta divisibility, scale growth and uniform face counting.')
source = re.sub(r'application_review=COMPONENTS\+\[.*?\]\+\[REMAINING\],',
    lambda _: 'application_review=COMPONENTS+'+repr(reviews)+'+[REMAINING],', source)
source = source.replace('08_alignment lines 550-567: signed residue-preserving face translations',
    '08_alignment lines 550-567: actual canonical face-shift counting')
Path('round-canonical-face-counting-audit.py').write_text(source, encoding='utf-8')
