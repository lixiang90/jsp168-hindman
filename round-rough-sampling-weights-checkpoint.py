from pathlib import Path
import json

v = json.loads(Path('round-rough-sampling-weights-checks.json').read_text(encoding='utf-8'))
r = json.loads(Path('round-rough-sampling-weights-review.json').read_text(encoding='utf-8'))
s = Path('CONTINUATION.txt').read_text(encoding='utf-8')
s = s.replace('Current batch: round-rough-induced-approximation', 'Earlier batch: round-rough-induced-approximation')
a = s.index('Immediate next work:')
b = s.index('The uniform rough-step theorem', a)
summary = (f"Current batch: round-rough-sampling-weights, verified 2026-10-11. Ten modules, "
    f"{v['new_theorems']} theorems, {v['new_definitions']} definitions; full build {v['build_jobs']} jobs; "
    f"{v['project_modules']} project modules; {v['selected_axiom_reports']} selected transitive axiom reports. "
    'Retained sources and axiom sets unchanged, standard axioms only, pinned paper sections matched. '
    'Author-side verification, not independent kernel replay.\n')
summary += '\n'.join('- ' + c for c in r['application_review'][:10]) + '\n'
summary += ('Review: Section 06 actual coprime sample intersection, original normalized piece weights, '
    'fixed finite-piece O(t/Z) total difference, positive pieces under explicit side thresholds and '
    'original uniform label-fiber convex selection are proved. A numeric weight comparison for a list '
    'of rectangular pieces is not yet a geometric partition. The label-fiber geometry and all asymptotic '
    'thresholds must be assembled before applying it to the original descent.\n\n')
summary += ('Immediate next work: construct the bounded rectangular subbox partition with uniform upper '
    'and lower side bounds and prove its finite label fibers, including K residues, are exactly the '
    'actual box pieces. One useful construction uses integer cuts A+(B-A)*i/N for i=0,...,N with fixed N. '
    'Its side lengths differ from (B-A)/N by less than one using integer remainder bounds, so sufficiently '
    'large original sides give comparable pieces. Finset.Ico_union_Ico_eq_Ico can telescope adjacent '
    'intervals; actual label fibers must be proved equal to the coordinate product subboxes. The earlier '
    'AlignedIntervalResiduePartition and CompleteResidueCellPartition give exact aligned-grid partitions '
    'and may also be useful, but their final clipped cells cannot silently be claimed to have a lower '
    'side bound. Then assemble RoughFiniteBoxWeightComparison, RoughUniformFiberMixture and '
    'RoughUniformFiberSelection with actual labels, frozen tests and the uniform finite-residue '
    'Lipschitz approximants, accounting for all 2(epsilon_freeze+epsilon_approx) losses. '
    'The original interval weight bound is 5t/length and the finite-box bound is '
    'card(pieces)*dimension*5t/(cZ), requiring sides >=cZ and 2t<=cZ. Each conditional residue '
    'intersection is nonempty if each piece side >=2tK. Prove these thresholds uniformly from the '
    'original rough-factor bounds; keep N,K and the number of pieces fixed before varying sample z '
    'and endpoints. Package the smaller rational character kernel as NativeNilmanifoldData with the '
    'proved compatible pullback metric, retaining Lie group, rational module and strict dimension '
    'decrease. Continue quantitative Leibman, corrected box comparison, affine coefficient identity, '
    'stretched filtration, finite density and uniform dimension induction.\n\n')
s = s[:a] + summary + s[b:]
Path('CONTINUATION.txt').write_text(s, encoding='utf-8')
print('Updated verified original sampling-weight checkpoint.')
