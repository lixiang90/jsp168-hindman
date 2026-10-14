from pathlib import Path
import importlib.util
import re

spec = importlib.util.spec_from_file_location('previous', 'round-harmonic-correlator-transfer-audit.py')
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
source = Path('round-harmonic-correlator-transfer-audit.py').read_text(encoding='utf-8')
source = source.replace('"""Register and audit original harmonic correlator transfer and the good-cell projection implication."""',
    '"""Register and audit finite native good-cell selection and actual master projection geometry."""')
source = source.replace("PREFIX = 'round-harmonic-correlator-transfer'", "PREFIX = 'round-native-good-cell-assembly'")
source = source.replace("OLD = 'round-period-correlation-transfer'", "OLD = 'round-harmonic-correlator-transfer'")
modules = ['Hindman168/NativePieceFiniteSelection.lean', 'Hindman168/InjectiveOptionSelection.lean',
    'Hindman168/NativeGoodCellAssembly.lean', 'Hindman168/NativeFiniteCellProjection.lean',
    'Hindman168/MasterCompleteCellProjectionGeometry.lean', 'Hindman168/MasterFiniteCellRecipeProjection.lean']
components = ['Finitely many actual native representing families can now be selected independently on each stage and original interval-residue piece, with a zero branch. Their finite product manifold and uniform observable bounds cover every choice, while unit pointwise bounds remain unit. An injective option selector selects exactly the admissible complete-cell label or zero, including empty admissible cell sets. Given a fixed finite list of actual unit native families and one locally correlating list member on every good cell, the proved selector constructs a global unit native family with the same good-cell correlations, zero on bad-cell points, zero off the complete-cell union and zero outside the admissible stage set. The original-law fine projection lower bound is consequently derived without assuming a global correlating family. For the actual master family, the original admissible complete-cell set is explicitly defined using its aligned integer endpoints and coprime residues. Master conditions discharge the original cell geometry, identify the actual complete-cell total mass with the aligned interior mass and prove that it tends to one. The actual M*(R/M)/X error tends to zero by the existing endpoint rate and the exact divisibility identity M*(R/M)=R. The assembled finite-list correlation-to-projection implication is instantiated on the actual master harmonic law and tail-containing ultrafilter, with no remaining cell-geometry or mass-limit input. Existence of the finite native recipe families with the displayed local inverse correlations remains an explicit unproved input, not an axiom or a proof of the unconditional inverse theorem.']
gap = 'Inverse correlator existence and uniform finite-list assembly of the native good-cell family, discharge of the displayed actual master-law geometry and limit inputs, and remaining replica integration remain missing.'
assert gap in previous.REMAINING
remaining = previous.REMAINING.replace(gap, components[0] +
    ' Inverse correlator existence and construction of the finite actual native recipe families from the raw finite nilmanifold inverse conclusion, quantitative uniform inverse thresholds and remaining replica integration remain missing.')
for field, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + field + r' = .*$', field + ' = ' + repr(value), source, flags=re.M)
counts = {'1172': '1178', '1160': '1166', '5394': '5407', '1178': '1184', '1169': '1175'}
source = re.sub(r'\b(?:1172|1160|5394|1178|1169)\b', lambda m: counts[m.group()], source)
source = source.replace('== len(set(names)) == 10', '== len(set(names)) == 13')
source = source.replace("'selected_report_count': 10", "'selected_report_count': 13")
source = source.replace('len(names) == 10', 'len(names) == 13')
source = source.replace("for kind, _ in values) == 10", "for kind, _ in values) == 12")
source = source.replace("'theorem_count': 10", "'theorem_count': 12")
source = source.replace('new_theorems=10', 'new_theorems=12')
source = source.replace('new_theorem_count=10', 'new_theorem_count=12')
source = source.replace('new_definitions=0', 'new_definitions=1')
source = source.replace('new_axiom_reports=10', 'new_axiom_reports=13')
source = source.replace('new_selected_report_count=10', 'new_selected_report_count=13')
source = source.replace("'Hindman168.integerCubeResidueShift'}",
    "'Hindman168.integerCubeResidueShift', 'Hindman168.admissible_option_selection_none'}")
review = [
    'PROGRESS. The preceding original harmonic correlator transfer round was terminal-successfully rechecked before edits. Its authoritative verification manifest was copied unchanged to this round baseline. Retained proof-source hashes and selected axiom sets remain unchanged, except for the necessary root imports and declaration registry.',
    'For a fixed native manifold, every member of a finite represented family receives common finite observable and Lipschitz bounds from the retained finite-bounds theorem. An Option-valued selection may vary by stage and actual interval-residue piece. Its observable, translating element and basepoint are selected together; the none branch uses the constant zero observable. Both branches satisfy the same bounds. Exact evaluation uses the original piece map and original linear orbit.',
    'Finitely many originally distinct native manifolds are first placed on their genuine native product by the retained common-manifold construction. The previous selector then gives one actual native representation for arbitrary per-piece selections. Pointwise unit bounds are preserved exactly by case analysis on the selected label, even though the common observable bound is allowed to depend on the finite list.',
    'The admissible option selector uses injectivity of the actual cell label. It returns each admissible preimage at its label and proves that every some output is admissible and has that same label. Nonadmissible labels give none. Empty admissible sets require no existence assumption and give the zero branch.',
    'Actual complete-cell labels (k,r) map injectively to (k,(r.val:integer)). On admissible stages, actual M*q=R and the existing exact piece-membership theorem identify every original complete-cell point with that same label. The selector chooses a locally correlating member of the fixed finite native recipe family independently on each good cell. The selected global family agrees with that recipe on all points of the cell, so its original uniform cell correlation is retained exactly.',
    'Bad cells are rejected by the injective selector and their actual cell-point values are exactly zero. Outside the actual union of selected complete cells, a some output would imply membership in one such cell, a contradiction. Stages outside the admissible geometry-and-local-correlation set are zero everywhere. Thus a bounded native correlating family is constructed rather than assumed; no original mass outside the chosen union is silently renormalized.',
    'The admissible stage set is the intersection of the eventual actual geometry and finite-list local-correlation conditions. On that same ultrafilter-large set, the constructed family is placed in the original integer harmonic bounded Hilbert family by the proved subprobability norm bound. The retained good-cell projection theorem supplies projection norm at least delta^(2^d)*gamma/2 from the original weighted global norm input. No new inverse-existence axiom is introduced.',
    'masterCompleteCells is exactly the actual aligned integer interval indices paired with original residues coprime to the original primorial. Master conditions give positive M and q=R/M and the exact identity M*q=R. The aligned endpoint inequalities and actual finite interval membership give every selected cell its required lower and upper physical endpoints. The original harmonic normalizer is positive eventually by the retained actual raw geometry.',
    'The complete-cell mass sum is identified with the actual aligned interior mass, using the existing admissible cell sum and exact finite product/subtype sum identities. This retains the original integer masses and proves total complete-cell mass tends to one by the already proved master interior limit. The period-to-cutoff error is exactly R/X by divisibility and is bounded by the retained primorial*(R+1)/X endpoint rate. Nonnegativity and that rate give the actual error limit zero without changing the scales.',
    'The final master theorem applies the constructed finite-list correlation-to-projection result on the actual master family, original integer harmonic law, original fine native projection and same tail-containing ultrafilter. All geometry and limit inputs in the prior projection theorem are discharged from MasterParameterConditions. The remaining displayed inverse input is existence of finite actual native unit recipe families with the required local correlations; converting a raw finite nilmanifold inverse statement to those families and proving that inverse statement are not claimed here.',
    'Development failures were resolved before registration: explicit constant-map Lipschitz coercion, removal of an unused simplification argument, exact subtype-sum and product-sum identities, let-bound arithmetic normalization, and explicit positive cyclic-order instances. No set_option or increased resource limit is used. Only warning-free terminal focused compilations, full build and complete selected kernel output count as verification.',
    'Six new modules contain twelve theorems and one definition, all selected for transitive axiom audit. The original final target remains unchanged and unproved. Inverse existence, native finite-family synthesis and quantitative thresholds, remaining replica integration, coloring-derived targets, Calibration/Alignment and final positive rapidly separated monochromatic extraction remain. No unavoidable blocker is established. Public repository, prize PR and claim remain pending.'
]
start = source.index('    review = dict(', source.index('def record():'))
end = source.index('    manifest = dict(baseline)', start)
source = source[:start] + (
    "    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,\n"
    '        application_review=' + repr(review) + ', new_modules=MODULES, verified=summary, remaining=REMAINING,\n'
    "        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='05_prediction: finite native recipe selection, good-cell assembly and original master fine-projection lower bound')\n"
) + source[end:]
Path('round-native-good-cell-assembly-audit.py').write_text(source, encoding='utf-8')
print('Prepared six-module audit: twelve theorems, one definition.')
