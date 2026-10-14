from pathlib import Path
import ast
import re

source=Path('round-exposed-cube-data-audit.py').read_text(encoding='utf-8')
modules=['FiniteComplexSetMean','AlignmentIntervalMeans','AlignmentClassCounts',
         'AlignmentEndpointMeanError','AlignmentActualEndpointMean','AlignmentBoxMeans',
         'AlignmentRetainedClassMean','AlignmentActualClassCounts']
components=[
    'Normalized complex means on finite sets now have exact injective-image transport, correct cardinal normalization (including empty targets), a uniform norm bound, and a symmetric-difference error at most twice the test bound times the changed-point count divided by the original cardinality.',
    'The original affine/cube-base interval sample-set identities now give exact normalized means, retaining the full transformed residue class. Aligning interval endpoints preserves the restricted mean exactly. Arbitrary signed residues have a uniform count error at most one and nonempty classes once the side length is at least twice the modulus.',
    'Forward endpoint movement by at most D changes each one-dimensional unrestricted bounded-test mean by at most 4*K*D/(U-L). Actual master growth makes this error arbitrarily small for alignment by d times the actual tail product, uniformly in samples, endpoints, residues and bounded tests, under the explicit side lower bound c*Z.',
    'Full finite product boxes have exact cardinal products, nonemptiness from per-side length bounds, and exact affine normalized-mean transport. Aligning endpoints to a coarse retained class and then dividing by the retained integer step gives an exact full-box sampling identity. No coprimality of retained and removed factors is used.',
    'For the actual master cube scale and full step d*t, one eventual threshold proves every allowed one-dimensional class nonempty and its cardinality times d*t divided by side length within epsilon of one, uniformly in all samples, signed endpoints and residues. The side lower bound remains explicit.'
]
reviews=[
    'Reviewed normalization at empty sets: the finite mean is zero there; the error theorem requires only the original set nonempty, and does not silently cancel a zero target cardinality.',
    'Reviewed restricted versus unrestricted endpoint movement: exact equality is proved only on the retained congruence class. Unrestricted means use the separate symmetric-difference bound.',
    'Reviewed coarse endpoint alignment before division: finer classes lie inside the chosen coarse class, both endpoints reconstruct exactly after integer division, and the transformed finer class is preserved. No inverse of the removed factor or retained/removed coprimality is introduced.',
    'Reviewed uniform quantifier order: actual scale thresholds precede sample, endpoint, residue and test choices. All limit applications retain c*Z as an explicit side lower bound; neither uniform transformation of every permitted original box nor a multidimensional endpoint-error conclusion is claimed.',
    'Pinned 08_alignment lines 392-401 assume original side lengths at least c*N_loc. The remaining geometry obligation is to transfer this input uniformly through integer rounding and the actual coordinate map, not to replace arbitrary boxes by one chosen box.',
    'All retained proof sources and transitive axiom sets are unchanged. This is author-side verification, not an independent kernel replay or proof of StrongConjecture.'
]
remaining=(
    'StrongConjecture remains unproved; no unavoidable obstruction is established. '
    'Exact normalized affine and retained-step box sampling, arbitrary-residue counting, one-dimensional endpoint errors '
    'and their uniform actual-master-scale bounds are now proved. Construct actual microcell origins; derive transformed '
    'common-scale location and side bounds uniformly for every permitted original box, whose side lower bound c*N_loc '
    'is a hypothesis of the paper, including integer endpoint rounding. Extend endpoint errors to full multidimensional box tests. '
    'Connect the normalized-box identities and counts to the actual conditional cube laws. '
    'The complete exposure fixes the degree-two scalar exponent polynomial, with exact original evaluation; '
    'substitute the actual tail product and cube vertex and prove bounded-degree joint native BCH log-polynomiality. '
    'Prove and apply the uniform rough-step proposition of section 06, with uniformity in coefficients, endpoints, residues '
    'and tests. Buffered short-bin geometry, prior-event positive probability, posterior control after additional prior '
    'conditioning, quantitative smooth-observable bounds, conditional face invariance and positive-probability Alignment '
    'remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence '
    'inputs. Complete final ordered positive rapidly separated monochromatic extraction. '
    'Existing conditional theorems and standard-only axiom reports are not a full proof. '
    'No independent kernel replay, external review, public contribution or prize submission is claimed.'
)
replacements=dict(PREFIX='round-normalized-box-counting',OLD='round-exposed-cube-data',
    MODULES=['Hindman168/'+m+'.lean' for m in modules], COMPONENTS=components, REMAINING=remaining)
lines=source.splitlines(keepends=True)
for node in reversed(ast.parse(source).body):
    if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name):
        name=node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno]=[name+' = '+repr(replacements[name])+'\n']
source=''.join(lines)
source=source.replace('Audit actual exposed cube data, scalar polynomial evaluation and dyadic scale divergence.',
                      'Audit exact normalized box means, residue counts and uniform endpoint errors.')
source=re.sub(r'application_review=COMPONENTS\+\[.*?\]\+\[REMAINING\],',
              lambda _: 'application_review=COMPONENTS+'+repr(reviews)+'+[REMAINING],',source)
source=source.replace('08_alignment lines 425-550: complete exposed cube data and dyadic scale divergence',
                      '08_alignment lines 482-567: normalized box sampling, retained steps and endpoint errors')
start=source.index("    rough = obj('round-cube-coordinates-rough-step-reference.json')")
end=source.index("    for section in fixed['sections']:",start)
source=source[:start]+"    assert len(fixed['sections']) == len({s['path'] for s in fixed['sections']}) == 6\n"+source[end:]
Path('round-normalized-box-counting-audit.py').write_text(source,encoding='utf-8')
