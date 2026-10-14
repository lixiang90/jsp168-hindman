from pathlib import Path
import ast
import io
import json
import tokenize

modules = ['Hindman168/' + n + '.lean' for n in [
    'MaskColorFamilyCoarseDualControl', 'NativeMetricMaskModelTesting',
    'MaskColorBlockNativeTesting', 'NativeCoarseProjectionTesting',
    'MaskColorCoarseNativeTesting', 'SelectedColorBlockCoarseTesting',
    'SelectedColorNativeTestingModels']]
components = [
    'Every tracked block transfers the same preselected color dense model to actual original chain dual control at each permissible gap. Only that tracked tail and pivot are required to bracket the gap, so its own selected coarse padding is permitted without imposing the common fine gap on other columns.',
    'The prescribed native quotient metric induces exactly the natural quotient topology, proved from the native metric quotient-map property. Actual lower-central cube compactness and natural quotient compactness are transported to that metric topology without changing the distance or Lipschitz constants. Original zero-prime testing now applies uniformly to the actual step-bounded native test recipes.',
    'Actual color dense-model dual control proves original harmonic rho-F native testing at every valid block gap. The original native family retains all stages and its prescribed metric; the zero-prime component of the actual template catalogue supplies the tests at dimension s+1. No inverse existence assumption is used for this testing step.',
    'Coarse projection approximation controls the original completed Hilbert pairing with every actual native unit-bounded coarse family. Orthogonality identifies the f pairing with its coarse projection, and the original subprobability law proves the test norm bound at every stage. The original expectation ultralimit then gives the eventual f-S test estimate.',
    'The actual rho-F limit and f-S coarse approximation combine to an eventual original rho-S test bound below the projection accuracy plus any positive slack. The same f, S, native test, master coefficient and original pivot mass are retained throughout; no inverse hypothesis or assumption of rho-F testing is inserted.',
    'For the actual selected principal indices, a valid nonempty tail preceding its pivot also precedes its own coarse padding. The exact masterGapIndex at that padding constructs the permissible block gap. A raw globally unit-bounded native test is realized in the same original Hilbert law without altering any stage.',
    'The same selected coloring native model family now simultaneously retains coarse native representation, projection accuracy, global unit bounds, all original rho-S subset-count replacements and one common native manifold, and additionally satisfies original rho-S coarse native testing at each valid selected block. The inverse existence inputs remain explicit and unproved. Each test family is fixed before its eventual stage; no uniform stage over all native families is claimed.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'The finite-list native periodic interval inverse existence statement remains an explicit unproved hypothesis; '
    'its genuine existence proof and positive uniform correlation constants must be supplied. '
    'The same actual coloring dense Hilbert family now supports selected native models, the complete original '
    'rho-S subset-count replacement and own-coarse-gap native testing, conditional on those inverse inputs '
    'for the selected model existence. The coarse testing transfer itself has no inverse hypothesis. '
    'The full coloring Prediction Principle still requires its calibration against actual product sampling, '
    'parameter and output integration. Calibration/Alignment and the final ordered positive rapidly '
    'separated monochromatic extraction remain incomplete. No unavoidable blocker is established. '
    'A complete public proof repository, official contribution PR, independent review and prize application '
    'remain pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The preceding coloring Hilbert-family audit was terminal-successfully rechecked and its unchanged authoritative manifest copied before these proof edits. The immediately preceding goal turn proved the last native block testing lemma after resolving definitional identifications, and verified official rules continue to accept complete Lean contributions. No completed prize proof or eligibility is claimed.',
    'The actual tracked-block template control is transferred at the same tail and pivot. Its gap need only follow this tail and precede this pivot. This correctly permits each block own coarse padding, rather than imposing the fine gap conditions simultaneously on unrelated columns.',
    'Natural quotient topology and the topology of the prescribed native metric are proved equal from the actual metric quotient-map property. Explicit equality transport carries the original compact quotient and the proved lower-central corner cube compactness to that topology. This avoids silently choosing another metric or assuming unproved layer compactness.',
    'The zero-prime member of the original dual catalogue has arity zero and dimension s+1. The native step bound is s, so its lower-central filtration is terminal at s+1. Each actual stage-varying native recipe is supplied as an admissible test to the proved uniform original-law testing theorem. The original weight and actual pivot law are preserved.',
    'The coarse Hilbert test is proved by projection orthogonality and Cauchy-Schwarz. Every original pivot law is a subprobability law at all stages, including possible zero initial laws, so the globally unit-bounded test has completed norm at most one without changing early stages. The exact completion linear map identifies f-S, and the original pairing convergence yields an eventual expectation bound.',
    'The rho-S identity is the exact sum of rho-F and F-S pairings. The actual rho-F theorem supplies vanishing error, and the same model coarse projection supplies the second bound. Half-slack bounds and the real triangle inequality prove the result for any positive slack without a new inverse assumption.',
    'Actual selected tail positions image lies in the selected principal set. The retained energyTail_before_padding theorem gives all tail indices before the selected own padding, while padding is before the pivot. The proved masterGapIndex value is used on its actual master range; its stage-constant definition preserves the given coarse native representation and projection approximation.',
    'The assembly selects exactly the f and S witnesses from the retained coloring selected model theorem, preserving all earlier count replacements, unit bounds and common native geometry. The additional raw native testing property refers to those exact S witnesses. Each v and slack are quantified before the eventual stage. It does not assert a single stage uniform over arbitrary bounded-complexity classes, nor erase the explicit interval inverse existence premise.',
    'All thirteen new theorems are selected for transitive kernel audit. Focused compilation, complete build, kernel audit and authoritative recheck must all finish successfully without warnings. No new definitions, instances, resource options, proof axioms or forbidden proof steps are introduced.',
    remaining
]

source = Path('round-color-block-hilbert-family-audit.py').read_text(encoding='utf-8')
# Rewrite numeric tokens, not substrings of counts or review prose.
mapping = {'1222':'1228', '1228':'1235', '1210':'1217', '1219':'1226',
           '5501':'5514', '12':'13', '10':'13'}
tokens = []
for token in tokenize.generate_tokens(io.StringIO(source).readline):
    if token.type == tokenize.NUMBER and token.string in mapping:
        token = token._replace(string=mapping[token.string])
    tokens.append(token)
source = tokenize.untokenize(tokens)
source = source.replace('new_definitions=2', 'new_definitions=0')
source = source.replace('new_module_count=6', 'new_module_count=7')
tree = ast.parse(source)
lines = source.splitlines(keepends=True)
replacements = []
values = {'PREFIX':'round-color-native-testing', 'OLD':'round-color-block-hilbert-family',
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
source = source.replace("reference_scope='05_prediction: one coloring Hilbert family and actual selected native rho-S count replacement'",
    "reference_scope='05_prediction: original rho-S coarse native testing on the same selected models'")
source = source.replace('manifest.update(files=files,', "manifest.update(date='2026-10-11', files=files,")
ast.parse(source)
Path('round-color-native-testing-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules':len(modules), 'expected_new_theorems':13, 'baseline_hashes':1228,
                  'current_modules':1217, 'current_reports':5514}))
