from pathlib import Path
import ast
import io
import json
import re
import tokenize

modules = ['Hindman168/' + n + '.lean' for n in [
    'NativeCalibrationCutoff', 'FiniteCutoffCalibration', 'MaskColorCoarseCalibration',
    'OriginalBlockProductTesting', 'MaskColorProductCalibration',
    'SelectedColorBlockProductCalibration', 'SelectedColorCalibratedModels']]
components = [
    'The paper calibration cutoff is explicitly 1 minus the unit clipping of (x-2*tau)/tau. It lies in [0,1], equals one below 2*tau and zero above 3*tau, has a proved finite Lipschitz bound for positive tau, and satisfies x*cutoff(x) <= 3*tau for nonnegative x. Composition preserves the same actual native quotient, prescribed metric and orbit.',
    'A proved finite weighted calibration inequality bounds the small-model color event by the cutoff error plus 3*tau. The original mass need only be a nonnegative subprobability law, and the color weight may be unbounded. No normalization by a color event mass is used.',
    'Actual original rho-S coarse testing applies to the cutoff of the same chosen native model. The original harmonic color event is eventually below 3*tau plus its actual coarse projection accuracy and arbitrary positive slack. This transfer has no inverse existence hypothesis.',
    'The actual integer block product law is defined using the original harmonic tail product and original pivot sample. Its divisor comparison expectation is exactly the original pivot expectation with the actual master block mask. The existing proved sampling growth and product-law error estimates give distance convergence to zero and an eventual bound uniform over all globally unit-bounded scalar tests.',
    'The actual block-product color-and-small-model event now satisfies calibration below 3*tau plus coarse projection accuracy and arbitrary positive slack. Its indicator uses the same original natural color coefficient and its expectation under the comparison law equals the original weighted color event exactly. The sampling error is derived from the original product law, not inserted as a premise.',
    'At selected principal coordinates, every valid nonempty tail precedes the same selected own coarse padding. The exact masterGapIndex agrees with that padding and preserves native representation and approximation. The block-product calibration theorem therefore applies to each exact chosen model.',
    'One selected model family now simultaneously retains native coarse representation, projection accuracy, global unit bounds, original rho-S native testing, original rho-S subset-count replacement, a common native manifold and the actual block-product calibration property. The inverse existence hypothesis remains explicit and unproved. The calibration threshold and coarse approximation accuracy are kept separate.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'The finite-list native periodic interval inverse existence statement remains an explicit unproved hypothesis; '
    'its genuine existence proof and positive uniform correlation constants must be supplied. '
    'The same actual selected coloring model family now supports original rho-S subset-count replacement, '
    'own-coarse-gap native testing and actual block-product calibration, conditional on the inverse inputs '
    'for selected model existence. The testing and calibration transfers themselves have no inverse hypothesis. '
    'The full Prediction Principle still needs a coarse approximation tolerance cap chosen before the '
    'master count N: the retained selection currently chooses approximation accuracy kappa/4, which '
    'is not proved smaller than a separately requested calibration tolerance. Its calibration bound '
    'therefore explicitly retains that approximation error. Original global raw-coordinate transport, '
    'final bounded count distribution replacement, admissible parameter and output integration also remain. '
    'Alignment and final ordered positive rapidly separated monochromatic extraction remain incomplete. '
    'No unavoidable blocker is established. A complete public proof repository, official contribution PR, '
    'independent review and prize application remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The preceding original coarse native testing audit was terminal-successfully rechecked and its unchanged authoritative manifest copied before these proof edits. All retained proof sources, selected transitive axiom sets and pinned mathematical references must remain unchanged.',
    'The actual cutoff matches the paper transition interval [2*tau,3*tau]. Its proved Lipschitz constant is inverse tau, so positive tau is an explicit hypothesis. Observable composition uses the retained boundedPieceNilsequence_lipschitz_comp theorem on the same native data, metric, group and lattice. No replacement quotient or unsupported compactness assumption is introduced.',
    'The finite weighted inequality retains every original measure coefficient. Low model values make the cutoff exactly one; elsewhere nonnegativity bounds the event by the weighted cutoff pairing. The model-cutoff product is at most 3*tau and the original subprobability mass is at most one. Only the error pairing and the real triangle/order bounds supply the accuracy loss.',
    'The actual color weight is eventually nonnegative by the proved original mask theorem. The model is globally nonnegative and has its original native coarse representation. Its cutoff is globally unit bounded and defines an original bounded Hilbert family without changing initial stages. The proved original rho-S test estimate supplies calibration error, rather than assuming a calibration claim.',
    'The comparison measure support lies in the original pivot support because its pointwise density is the actual integer divisor mask. Expanding its expectation over that pivot support identifies exactly the original weighted expectation. The original product-distance convergence follows from actual master-chain sampling growth and the retained integer block product law. Its scalar testing bound is genuinely uniform over all unit-bounded functions at a stage.',
    'The original product event indicator is exactly positive integer input, the original natural master color coefficient and the small-model condition. This indicator is bounded by one and its weighted pivot expectation agrees with the original color-weight small-model event by pointwise case analysis. Half-slack for product testing and half-slack for coarse testing give the stated calibration bound.',
    'A decidability-instance mismatch between the event indicator and the local test is resolved by proving pointwise equality of their actual values, not by replacing either event. The original weighted law, model and color coefficient are unchanged.',
    'The selected calibration assembly preserves exactly the retained chosen f and S witnesses, all count replacements, native test estimates, unit bounds and common native geometry. Every test threshold is fixed before its eventual stage. The positive scalar cutoff threshold is separate from coarse approximation accuracy; no quantifier exchange or uniform stage over all thresholds is claimed.',
    'Proof review located a remaining tolerance issue in the retained finite_order_native_shortCube_models: its coarse approximation is kappa/4. That choice is sufficient for the inverse projection test but is not proved below a separately requested calibration tolerance. The current conclusion therefore states 3*threshold + approximation_error + slack. A future proof must choose a capped positive approximation accuracy, such as a minimum with a fraction of the requested tolerance, before selecting N, and carry it through the same energy model construction.',
    'All fourteen new theorems and both new definitions are selected for transitive kernel audit. Focused compilation, complete build, kernel audit and authoritative recheck must all finish successfully without warnings. No new instances, resource options, proof axioms or forbidden proof steps are permitted.',
    remaining
]

source = Path('round-color-native-testing-audit.py').read_text(encoding='utf-8')
mapping = {'1228':'1235', '1235':'1242', '1217':'1224', '1226':'1233',
           '5514':'5530', '13':'16'}
tokens = []
for token in tokenize.generate_tokens(io.StringIO(source).readline):
    if token.type == tokenize.NUMBER and token.string in mapping:
        token = token._replace(string=mapping[token.string])
    tokens.append(token)
source = tokenize.untokenize(tokens)
source, count = re.subn(r'(^    assert sum\([^\n]+\) == )16$', r'\g<1>14', source, flags=re.M)
assert count == 1
source = source.replace("'theorem_count': 16", "'theorem_count': 14")
source = source.replace('new_theorems=16', 'new_theorems=14')
source = source.replace('new_theorem_count=16', 'new_theorem_count=14')
source = source.replace('new_definitions=0', 'new_definitions=2')
tree = ast.parse(source)
lines = source.splitlines(keepends=True)
replacements = []
values = {'PREFIX':'round-color-native-calibration', 'OLD':'round-color-native-testing',
          'MODULES':modules, 'COMPONENTS':components, 'REMAINING':remaining}
for node in tree.body:
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in values:
            replacements.append((node.lineno-1, node.end_lineno, name+' = '+repr(values[name])+'\n'))
assert len(replacements) == len(values)
for start, end, text in reversed(replacements):
    lines[start:end] = [text]
source = ''.join(lines)
tree = ast.parse(source)
for node in ast.walk(tree):
    if isinstance(node, ast.keyword) and node.arg == 'application_review':
        old_review = ast.get_source_segment(source, node.value)
        assert source.count(old_review) == 1
        source = source.replace(old_review, repr(reviews), 1)
        break
else:
    raise AssertionError('review field missing')
source = source.replace("reference_scope='05_prediction: original rho-S coarse native testing on the same selected models'",
    "reference_scope='05_prediction: cutoff and original block-product calibration on the same selected models'")
ast.parse(source)
Path('round-color-native-calibration-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules':len(modules), 'expected_new_theorems':14, 'new_definitions':2,
                  'baseline_hashes':1235, 'current_modules':1224, 'current_reports':5530}))
