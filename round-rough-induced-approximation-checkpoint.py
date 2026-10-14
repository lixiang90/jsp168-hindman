from pathlib import Path
import json

v = json.loads(Path('round-rough-induced-approximation-checks.json').read_text(encoding='utf-8'))
r = json.loads(Path('round-rough-induced-approximation-review.json').read_text(encoding='utf-8'))
s = Path('CONTINUATION.txt').read_text(encoding='utf-8')
s = s.replace('Current batch: round-rough-slow-freezing', 'Earlier batch: round-rough-slow-freezing')
a = s.index('Immediate next work:')
b = s.index('The uniform rough-step theorem', a)
summary = (f"Current batch: round-rough-induced-approximation, verified 2026-10-11. Ten modules, "
    f"{v['new_theorems']} theorems, {v['new_definitions']} definitions; full build {v['build_jobs']} jobs; "
    f"{v['project_modules']} project modules; {v['selected_axiom_reports']} selected transitive axiom reports. "
    'Retained sources and axiom sets unchanged, standard axioms only, pinned paper sections matched. '
    'Author-side verification, not independent kernel replay.\n')
summary += '\n'.join('- ' + c for c in r['application_review'][:10]) + '\n'
summary += ('Review: Section 06 now has uniform prescribed-error bounded Lipschitz approximants on the actual '
    'compact conjugate kernel quotients, with a single constant for a fixed finite residue family and bounded '
    'scalar left parameters. The exact pullback metrics have the natural quotient topology and compactness proved. '
    'The original induced tests are NOT claimed Lipschitz in arbitrary compatible metrics. Two-law approximation '
    'and freezing losses are explicit. Smaller native nilmanifold data packaging, sampling comparison and '
    'dimension induction remain open.\n\n')
summary += ('Immediate next work: establish original residue sampling weights, exact mixture disintegration and '
    'subbox geometry before applying convex selection. Existing IntervalResidueCount proves location-independent '
    'one-coordinate count error <=1 for integerWindow(A,T), including negative endpoints. AlignmentClassCounts '
    'and AlignmentActualClassCounts also have original residue counts and normalized relative errors; '
    'AlignmentBoxMeans has actual finite coordinate product classes and affine images. FiniteMixture and '
    'FiniteEventMixtures retain original mass weights. Prove the actual coprime step-t/K residue restriction and '
    'uniform O(t/Z) total piece-weight comparison, with positive class sizes and exact normalization. '
    'The bounded number of subboxes and residue vectors must remain fixed before sample z and endpoints. '
    'Package the smaller rational character kernel as NativeNilmanifoldData with the new actual compatible '
    'pullback metric, retaining Lie group, rational module and strict dimension decrease. The native finite-residue '
    'approximation constant may depend on fixed native data, V, rational kernel, finite residue family, R,B,Lip '
    'and prescribed epsilon, but precedes every residue index, left scalar, original test and sample mass. '
    'Freeze and approximate at fixed errors small relative to eta; include 2(epsilon_freeze+epsilon_approx) '
    'before the existing reweighted convex-piece selection. Continue quantitative Leibman, corrected box '
    'comparison, affine coefficient identity, stretched filtration, finite density and dimension induction.\n\n')
s = s[:a] + summary + s[b:]
Path('CONTINUATION.txt').write_text(s, encoding='utf-8')
print('Updated verified induced-approximation checkpoint.')
