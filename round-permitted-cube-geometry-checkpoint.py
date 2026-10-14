from pathlib import Path
import json

p = Path('CONTINUATION.txt')
s = p.read_text(encoding='utf-8')
v = json.loads(Path('round-permitted-cube-geometry-checks.json').read_text())
assert v['full_target_proved'] is False
s = s.replace('Current batch: round-normalized-box-counting', 'Earlier batch: round-normalized-box-counting')
start = s.index('Review correction for the next step:')
end = s.index('Next algebra work:', start)
new = f'''Current batch: round-permitted-cube-geometry, verified 2026-10-11. Seven modules, {v['new_theorems']} theorems and {v['new_definitions']} definitions; full build ({v['build_jobs']} jobs), {v['selected_axiom_reports']} selected transitive axiom reports, {v['project_modules']} project modules. Retained proof sources and axiom sets are unchanged; standard axioms only. All six pinned paper sections match their Git objects. This is author-side verification, not independent kernel replay.
- AlignmentMicrocellFirst constructs the first residue point in the aligned microcell [(p/R)*R,(p/R)*R+R), proves its congruence, minimality, membership, distance <=R and the exact progression range 0<=ell<R/M. Euclidean division handles negative integer origins.
- AlignmentCeilBoxes proves the exact half-open integer sample set for arbitrary real endpoints via ceilings, including negative and integral endpoints. It bounds location and side-length rounding losses.
- AlignmentLocalLength defines the actual N_loc=Nat.sqrt(gap)/M, proves M*N_loc=R exactly and eventual growth, and discharges actual microcell-origin distance assumptions.
- AlignmentRoundedIntervals proves the exact actual microcell progression and absorbs rounding uniformly for every allowed real interval. Original c*N_loc lower sides become at least (c/2)*R after multiplication by M.
- AlignmentRoundedCubeGeometry and AlignmentCubeBoxCoordinates transfer EVERY original permitted box to the common scale Z. The base coordinate bound is [2^card(T)*(K+1)+2]*Z, increment bound 2^card(T)*K*Z, and side bounds (c/2)*Z and 2^card(T)*(2*C+1)*Z. Full cube-coordinate box images and normalized means agree exactly with transformed residue classes.
- AlignmentPermittedCubeSampling combines this geometry with actual full-step counts: one eventual w threshold precedes all positive tail samples, arbitrary permitted real endpoint boxes, residues and complex test functions. Both original and transformed sample boxes are nonempty, each transformed coordinate has relative normalized count error <=epsilon, and the full normalized mean transfer is exact. This is per-coordinate counting, not yet a multidimensional endpoint perturbation error estimate.

Proof review: pinned 08_alignment.tex lines 392-401 assumes arbitrary original boxes in [-C*N_loc,C*N_loc] with sides >=c*N_loc. The new theorems cover all such boxes; they do not narrow this quantifier to one chosen box. N_loc=R/M appears at line 279 and the progression at line 290. The frozen formula is expressly extended beyond the microcell at lines 414-417, so the bounded-multiple transformed box need not lie within that cell. No exact pivot microcell is added to the earlier short-exposure key. Y is explicitly the INTEGER quotient floor(Q/M). The location and side hypotheses previously explicit in round-cube-bounds now have this actual permitted-box bridge; probabilistic transfers remain separate.

Immediate next geometry work: prove uniform location/side geometry after retained-step integer endpoint division. AlignmentRetainedEndpoint_reconstruct gives a+D*endpoint(L)=alignmentResidueEndpoint(L,D,a). For 0<=a<D, the alignment remainder gives |D*endpoint(L)-L|<D; subtracting two endpoints cancels a and gives side error <D. Combine with D=o(Z) (available from actual retained-scale growth) to obtain fixed location bounds and positive lower sides at Z/D for all retained subsets and bounded CRT representatives. Exact retained box mean transport already exists in AlignmentRetainedClassMean. Extend one-dimensional normalized endpoint error to full product-box tests, e.g. product mean factorization and a coordinate telescoping estimate. Then connect full normalized sampling geometry to actual conditional marginal cube laws. No coprimality between removed and retained factors may be assumed.

'''
s = s[:start] + new + s[end:]
p.write_text(s, encoding='utf-8')
print('Updated continuation checkpoint from verified counts.')
