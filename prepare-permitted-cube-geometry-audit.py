from pathlib import Path
import ast
import re

source=Path('round-normalized-box-counting-audit.py').read_text(encoding='utf-8')
modules=['AlignmentMicrocellFirst','AlignmentCeilBoxes','AlignmentLocalLength',
         'AlignmentRoundedIntervals','AlignmentRoundedCubeGeometry','AlignmentCubeBoxCoordinates',
         'AlignmentPermittedCubeSampling']
components=[
    'The literal first point of the pivot residue class in the sampled aligned microcell is constructed. Its residue, minimality, cell membership, distance from the pivot, and exact progression parametrization are proved, including signed integer pivots.',
    'The actual local length is Nat.sqrt(gap)/M, satisfies M*N_loc=R exactly, and exceeds every fixed bound eventually by the existing master growth. Half-open real boxes have exact integer-ceiling sample sets; rounding costs at most one in endpoint and side comparisons.',
    'For every original real interval inside [-C*N_loc,C*N_loc] with side length at least c*N_loc, one uniform threshold yields the actual common-scale bounds after ceiling and cube coordinate transformation. Base and increment locations are bounded by fixed multiples of Z, and side lengths lie between (c/2)*Z and 2^card(T)*(2*C+1)*Z.',
    'The genuine full cube coordinate map treats the base and all increments together. It has exact affine image and normalized finite-mean identities on full product boxes with their transformed residue vector. The geometric threshold works uniformly over every permitted real box, not just a chosen example box.',
    'The complete permitted-cube sampling theorem combines actual geometry with actual residue counting. For all allowed real boxes and residue vectors it proves both original and transformed sample boxes nonempty, per-coordinate relative count error at most epsilon, and exact normalized complex-test transfer. It chooses the fixed auxiliary radius internally and adds no geometric assumption beyond the original box bounds.'
]
reviews=[
    'Reviewed pivot-origin construction with positive modulus and actual positive width: the first residue representative stays inside the aligned microcell because M divides R. No exact microcell is added to the earlier short-exposure key.',
    'Reviewed half-open conventions: ceil(L)<=z<ceil(U) is exactly L<=z<U for integer z, including integral and negative endpoints. Rounding is absorbed only after a threshold proving N_loc>=1 and c*N_loc>=2.',
    'Reviewed quantifiers against pinned 08_alignment lines 392-401: w is chosen before all sampled tuples, endpoints and residue vectors. Every box satisfying the original locality and side hypotheses is covered. The actual base coordinate uses the original integer Y=floor(Q/M).',
    'Reviewed normalization: source and target boxes are both proved nonempty, via the exact image and count bounds. The mean identity retains all congruence restrictions. Tests may be arbitrary complex functions because the transfer is exact.',
    'The paper extends the frozen formula beyond the microcell for bounded-multiple boxes (lines 414-417). The new sampling statements do not incorrectly require all cube vertices to stay in the actual pivot microcell. Probabilistic agreement with the original colored data and uniform native observable bounds remain separate obligations.',
    'All retained proof sources and transitive axiom sets are unchanged. This is author-side verification, not independent kernel replay or proof of StrongConjecture.'
]
remaining=(
    'StrongConjecture remains unproved; no unavoidable obstruction is established. Actual microcell origins, exact N_loc, '
    'uniform integer rounding and common-scale location/side bounds for every permitted original real cube box are now proved. '
    'The full exact coordinate image and normalized mean transfer, source/target nonemptiness and uniform per-coordinate '
    'relative counts are connected to those paper hypotheses. Extend one-dimensional endpoint errors to full product-box '
    'tests, and prove normalized retained-step location/side bounds after the exact integer endpoint division. '
    'Connect these normalized sampling results to the actual conditional marginal cube laws. '
    'Prove uniform-degree joint native logarithm polynomiality after substituting the exposed scalar exponent and tail product; '
    'the existing univariate native product-logarithm polynomial may provide a specialized route via g^k*x=x*(x^-1*g*x)^k. '
    'Prove and apply the uniform rough-step proposition of section 06, including coefficients, endpoints, residues and tests. '
    'Buffered short-bin geometry, prior-event positive probability, posterior control after additional prior conditioning, '
    'quantitative native smooth-observable bounds, conditional face invariance and positive-probability Alignment remain open. '
    'HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. '
    'Complete final ordered positive rapidly separated monochromatic extraction. Standard-only axiom reports do not prove '
    'the full target. No independent kernel replay, external review, public contribution or prize submission is claimed.'
)
replacements=dict(PREFIX='round-permitted-cube-geometry',OLD='round-normalized-box-counting',
    MODULES=['Hindman168/'+m+'.lean' for m in modules],COMPONENTS=components,REMAINING=remaining)
lines=source.splitlines(keepends=True)
for node in reversed(ast.parse(source).body):
    if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name):
        name=node.targets[0].id
        if name in replacements:
            lines[node.lineno-1:node.end_lineno]=[name+' = '+repr(replacements[name])+'\n']
source=''.join(lines).replace('Audit exact normalized box means, residue counts and uniform endpoint errors.',
                            'Audit actual microcell origins and uniform permitted cube-box geometry.')
source=re.sub(r'application_review=COMPONENTS\+\[.*?\]\+\[REMAINING\],',
              lambda _: 'application_review=COMPONENTS+'+repr(reviews)+'+[REMAINING],',source)
source=source.replace('08_alignment lines 482-567: normalized box sampling, retained steps and endpoint errors',
                      '08_alignment lines 273-290, 392-417 and 479-495: actual microcell and all permitted cube boxes')
Path('round-permitted-cube-geometry-audit.py').write_text(source,encoding='utf-8')
