from pathlib import Path
import ast
import re
import json

previous = 'round-mask-block-all-gap-models'
prefix = 'round-color-block-hilbert-family'
modules = [
    'Hindman168/MaskColorBlockHilbertFamily.lean',
    'Hindman168/MaskColorFamilyChainReplacement.lean',
    'Hindman168/MaskColorFamilySelectedQuality.lean',
    'Hindman168/MaskUnitNativeReplacement.lean',
    'Hindman168/MaskColorNativePredictionTransfer.lean',
    'Hindman168/SelectedColorDenseNativeModels.lean',
]
components = [
    'The actual all-gap coloring dense models now form one global unit-bounded '
    'family in the original pivot Hilbert spaces, constructed before the '
    'ultrafilter, energy indices and chains. Invalid block coordinates have a '
    'zero representative; every valid block retains all actual mask and '
    'zero-prime dual tests at all permissible gaps and positive quotient scales.',
    'That same family simultaneously replaces every nonsingleton color-weight '
    'factor in every later valid chain. Exact block-mask identification transfers '
    'the actual color bounds and actual template pairing proves rho-F cube '
    'convergence. The proved original finite telescoping bound controls '
    'replacement against arbitrary admissible companion factors and product masks.',
    'Actual selected principal coordinates give the block-range, common fine-gap '
    'and tail hypotheses for the same family. Its rho-F replacement quality '
    'holds at the actual first selected padding and transfers to any '
    'tail-containing ultrafilter with no new choice of dense models.',
    'An exact finite native replacement path turns F-S error correlations into '
    'a total bounded-model replacement error of L times the tested error, '
    'where L is the actual number of nonsingleton mask supports. Double subset '
    'replacement is exactly idempotent for the final models.',
    'The rho-F replacement and F-S estimates now combine on their actual '
    'constructed admissible error families along the same ultrafilter. No '
    'unproved uniform-stage estimate is inferred from a bound for arbitrary '
    'input sequences. The complete original rho-S subset replacement error '
    'is at most (L+1) times the tested accuracy.',
    'Given the still explicit finite list of interval inverse existence inputs, '
    'one actual coloring dense family chosen before all ultrafilters now '
    'supplies the same selected native coarse model family. All selected chains '
    'have both the actual rho-F replacement, the actual F-S target estimates '
    'and their proved total original rho-S subset-count replacement. The '
    'same native models retain their own coarse representations, projection '
    'accuracy, global unit bounds and common native manifold with uniform '
    'observable bounds. Analytic thresholds and required master count precede '
    'the coloring and coefficients.'
]
remaining = (
    'StrongConjecture and the original full finite monochromatic sums/products '
    'claim remain unproved. The finite-list native periodic interval inverse '
    'existence statement remains an explicit unproved hypothesis; its genuine '
    'existence proof and positive uniform correlation constants must be supplied. '
    'The same actual coloring dense Hilbert family now supports selected native '
    'models and the complete original rho-S subset-count replacement, conditional '
    'on those inverse inputs. This does not prove the entire coloring Prediction '
    'Principle: its remaining native/coarse testing, parameter and output '
    'integration must be completed. Calibration/Alignment and the final ordered '
    'positive rapidly separated monochromatic extraction remain incomplete. '
    'No unavoidable blocker is established. A complete public proof repository, '
    'official contribution PR, independent review and prize application remain '
    'pending; no completed prize submission is claimed.'
)
reviews = [
    'PROGRESS. The preceding all-gap color dense-model round was '
    'terminal-successfully rechecked and its unchanged authoritative manifest '
    'copied before proof edits. The present proof family preserves all earlier '
    'sources, selected axioms and pinned mathematical references.',
    'Every valid tail/pivot/color/coefficient block receives the actual model '
    'constructed by the prior all-gap theorem. Invalid coordinates are zero, '
    'so the energy input family is total and globally unit bounded. The '
    'original harmonic laws are subprobability laws at every initial stage; '
    'the retained original bounded-family constructor therefore supplies '
    'actual Hilbert membership without modifying initial stages.',
    'Actual chain color weights use the same original master coefficient and '
    'the same tail as the one-column block realization. The actual block '
    'divisor mask depends only on that tail. Selecting a later chain thus '
    'does not select another dense model. All nonsingleton replacements use '
    'the same original correlation, integer forms and product masks.',
    'The common fine padding is the first selected padding. The proved '
    'principal-coordinate recovery gives its order before every pivot and '
    'after every tail. The total masterGapIndex agrees with the actual '
    'padding on its proved master range, at every w.',
    'The bounded F-S path visits every actual nonsingleton mask support '
    'exactly once. Its error factor is bounded by one since both model '
    'values are in [0,1]; eventual nonnegativity of the original divisor '
    'mask gives the original admissibility bound. The exact update '
    'difference and finite real triangle inequality give L times the '
    'single-target accuracy. Singleton and product factors retain their '
    'original place in the actual count.',
    'The retained selected native theorem bounds every admissible input '
    'sequence; it does not state an arbitrary uniform-stage bound. The '
    'new transfer supplies only the finitely many actual intermediate '
    'error sequences needed for this input count and uses their proved '
    'eventual admissibility. Finite eventual intersection then suffices '
    'for the actual telescoping bound. This avoids an invalid quantifier '
    'exchange and needs no assumption of target cube smallness.',
    'The coloring dense family is chosen before the ultrafilter and selected '
    'indices. The same family is passed to the proved selected native model '
    'theorem, with all coarse representation, approximation, unit-bound '
    'and common native observable properties retained. The constructed '
    'rho-F and F-S estimates supply the full original rho-S subset-count '
    'replacement. The finite list of interval inverse existence '
    'hypotheses remains explicit throughout.',
    'All twelve new declarations are selected for transitive kernel audit. '
    'Focused compilation, complete build, kernel audit and authoritative '
    'recheck must all be warning-free and terminal successful. No new '
    'resource options or forbidden proof steps are permitted.',
    remaining,
]
source = Path(previous + '-audit.py').read_text(encoding='utf-8')
source = source.replace("PREFIX = '" + previous + "'", "PREFIX = '" + prefix + "'")
source = source.replace("OLD = 'round-mask-renamed-short-cube'", "OLD = '" + previous + "'")
for name, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + name + r' = .+$', name + ' = ' + repr(value), source, count=1, flags=re.M)
numbers = {'1218': '1222', '1222': '1228', '1204': '1210', '1213': '1219', '5489': '5501'}
source = re.sub(r'\b(?:1218|1222|1204|1213|5489)\b', lambda m: numbers[m.group()], source)
source = source.replace('== 16\n', '== 12\n')
source = source.replace("for kind, _ in values) == 12", "for kind, _ in values) == 10")
source = source.replace("'theorem_count': 12, 'selected_report_count': 16", "'theorem_count': 10, 'selected_report_count': 12")
source = source.replace('new_theorems=12, new_definitions=4', 'new_theorems=10, new_definitions=2')
source = source.replace('new_axiom_reports=16', 'new_axiom_reports=12')
source = source.replace('new_module_count=4, new_theorem_count=12', 'new_module_count=6, new_theorem_count=10')
source = source.replace('new_selected_report_count=16', 'new_selected_report_count=12')
source = re.sub(r'application_review=\[.*?\], new_modules=MODULES',
                'application_review=' + repr(reviews) + ', new_modules=MODULES', source, count=1, flags=re.S)
source = source.replace('05_prediction: all-gap block dense models and actual coloring rho-F subset correlations',
                        '05_prediction: one coloring Hilbert family and actual selected native rho-S count replacement')
source = source.replace('Register and audit all-gap block dense models and actual color weights.',
                        'Register and audit the common coloring Hilbert/native family and rho-S count replacement.')
ast.parse(source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules': modules, 'theorems': 10, 'definitions': 2, 'reports': 12}))
