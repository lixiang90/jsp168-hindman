from pathlib import Path
import ast
import io
import json
import tokenize

modules = ['Hindman168/' + n + '.lean' for n in [
    'FiniteOrderNativeShortCubeModelsCapped', 'FiniteOrderNativeChainPredictionCapped',
    'SelectedNativeMaskCorrelationCapped', 'SelectedColorDenseNativeModelsCapped',
    'SelectedColorNativeTestingModelsCapped', 'SelectedColorCalibratedModelsCapped',
    'SelectedColorCalibrationTolerance', 'OriginalBlockRawSampling',
    'SelectedColorGlobalCalibration']]
components = [
    'For every prescribed positive calibration tolerance cap, the actual coarse approximation accuracy is chosen as min(kappa/4,cap/2). It is proved positive, below cap and small enough for the same inverse projection threshold. This choice precedes the master index count N, coloring, coefficients, ultrafilter and selected indices.',
    'The capped approximation choice propagates through the actual finite-order native chain models, all original F-S correlations, the same coloring dense family and its native testing and product calibration assembly. All original probability laws, selected coarse representations, model unit bounds and common native manifold properties are retained.',
    'The same selected models now have original block-product calibration below 3*threshold plus the prescribed cap, with no residual approximation error in that bound. Since the actual coarse error is below cap, the remaining positive slack cap minus that error is supplied to the proved calibration theorem. The inverse existence hypotheses remain explicit and unproved.',
    'The complete original global raw harmonic coordinate law has exactly the original block-product marginal, eventually at all valid master stages. The proved global disjoint-statistics law and exact scalar marginalization integrate out unused coordinates using their actual proved mass one. Arbitrary scalar tests and events transfer exactly, with no bounded-test assumption or extra sampling error.',
    'The same capped model family now simultaneously has calibration below 3*threshold plus the prescribed tolerance under both the original block-product law and the complete global raw-coordinate law, together with the earlier original count replacement, coarse native testing and common native geometry. The raw product used in the event is the actual sampleProducts of the same selected block and uses the same original natural master coefficient.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. '
    'The finite-list native periodic interval inverse existence statement remains an explicit unproved hypothesis; '
    'its genuine existence proof and positive uniform correlation constants must be supplied. '
    'The same actual selected coloring model family now supports original rho-S subset-count replacement, '
    'own-coarse-gap native testing and calibration at a prescribed tolerance under both the original block '
    'product law and complete global raw-coordinate law, conditional on the inverse inputs for selected '
    'model existence. The coarse tolerance cap is proved and chosen before N; the former uncapped '
    'calibration error issue is resolved in the new capped route. Testing, calibration and raw marginal '
    'transport themselves have no inverse existence premise. The full Prediction Principle still needs '
    'final bounded count distribution replacement and admissible parameter, relabeling, tolerance and '
    'output integration. Alignment and final ordered positive rapidly separated monochromatic extraction '
    'remain incomplete. No unavoidable blocker is established. A complete public proof repository, '
    'official contribution PR, independent review and prize application remain pending; no completed '
    'prize submission is claimed.'
)
reviews = [
    'PROGRESS. The preceding original native calibration audit was terminal-successfully rechecked and its unchanged authoritative manifest copied before these proof edits. The prior round exposed an uncapped coarse approximation choice. This round proves a capped route without changing retained proof sources.',
    'The actual finite-order short-cube threshold theorem fixes J and kappa first. The new coarse error is min(kappa/4,cap/2), where cap is prescribed before all master data. Positivity, strict cap bound and twice-error below kappa are proved by real order inequalities. The same concrete selected energy theorem is then called at that chosen error before selecting N.',
    'The capped witness is transported through the existing proof construction rather than inserted as an additional unproved premise. New modules preserve every native representation, unit bound, original law and the actual short-cube/correlation conclusions. Neither the native step bound nor the explicit finite inverse existence hypothesis is weakened or removed.',
    'The coloring dense family is still constructed before the ultrafilter and selected indices. Each assembly passes the same chosen f to the capped energy model construction and preserves the same S family in all subsequent statements. No later calibration threshold or stage chooses another dense or native model.',
    'Original product calibration retained its coarse-error term plus arbitrary positive slack. The capped error is strictly below cap, so cap-error is positive. Applying the actual calibration theorem at this slack gives the strict eventual bound 3*threshold+cap. Both the approximation error and the requested cap are fixed before N; the cutoff threshold is fixed before its eventual stage.',
    'The global raw-coordinate transport is exact after the actual normalizers become positive. The retained global_chain_coordinate_mass theorem identifies disjoint block statistics, and expectation_piMass_coordinate marginalizes the one-column statistic with its derived total one. Tail mass one follows from actual valid cutoffs; pivot mass one follows from the actual positive harmonic normalizer. All unused original coordinates retain their original laws.',
    'Arbitrary original scalar tests transfer exactly to the integer block law through its actual natural-number pushforward. Event transfer is the same identity applied to the actual event indicator. No artificial probability normalization, counting measure, bounded input restriction or assumed sampling-law identification is added.',
    'The global calibration assembly uses the same selected model witnesses as the proved capped product calibration, native testing and original subset-count replacement. Its raw event is evaluated at the actual one-block sampleProducts on Fin M raw coordinates, using the same natural master color coefficient and positive-integer convention.',
    'Nine new modules contain ten theorems, with no new definitions, instances or resource options. Focused checks, sequential dependency builds, the complete project build, transitive kernel audit and authoritative recheck must all finish successfully without warnings. All retained proof hashes and selected axiom sets must remain unchanged except the root import and registry files.',
    remaining
]

source = Path('round-color-native-calibration-audit.py').read_text(encoding='utf-8')
mapping = {'1235':'1242', '1242':'1251', '1224':'1233', '1233':'1242',
           '5530':'5540', '14':'10', '16':'10', '7':'9'}
tokens = []
for token in tokenize.generate_tokens(io.StringIO(source).readline):
    if token.type == tokenize.NUMBER and token.string in mapping:
        token = token._replace(string=mapping[token.string])
    tokens.append(token)
source = tokenize.untokenize(tokens)
source = source.replace('new_definitions=2', 'new_definitions=0')
tree = ast.parse(source)
lines = source.splitlines(keepends=True)
replacements = []
values = {'PREFIX':'round-calibration-tolerance-cap', 'OLD':'round-color-native-calibration',
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
source = source.replace("reference_scope='05_prediction: cutoff and original block-product calibration on the same selected models'",
    "reference_scope='05_prediction: capped tolerance chosen before N and exact global raw-coordinate calibration'")
ast.parse(source)
Path('round-calibration-tolerance-cap-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules':len(modules), 'expected_new_theorems':10, 'new_definitions':0,
                  'baseline_hashes':1242, 'current_modules':1233, 'current_reports':5540}))
