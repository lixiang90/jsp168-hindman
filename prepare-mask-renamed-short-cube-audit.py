from pathlib import Path
import ast
import json
import re

previous = 'round-original-short-cube-law'
prefix = 'round-mask-renamed-short-cube'
modules = [
    'Hindman168/RenamedPrimeShortCubeLaw.lean',
    'Hindman168/MaskRenamedShortCubeLaw.lean',
    'Hindman168/MaskNativeModelShortCubeThreshold.lean',
    'Hindman168/MaskNativeModelCorrelationThreshold.lean',
    'Hindman168/MaskMasterGapIndependence.lean',
    'Hindman168/SelectedChainMaskShortCubeTransfer.lean',
    'Hindman168/SelectedNativeMaskCorrelation.lean',
]
components = [
    'Finite conditional expectations commute exactly with the original pushforward, '
    'including zero event masses. Bijective local prime-slot renaming preserves '
    'primeSampleGood, including its distinct-prime condition. The actual polynomial '
    'short-cube statistic and its original absolute prime-good expectation are exactly '
    'preserved under this renaming.',
    'Every actual mask row has the full master prime arity. Its concrete slot map is '
    'the finite-index bijection. The actual renamed local catalogue is nonzero by '
    'proved master inclusion, and its actual local weak-prime-good short-cube mean '
    'equals the corresponding original master mean with no marginalization error.',
    'Given the explicit finite list of interval inverse existence inputs, one J and '
    'one positive fine-projection threshold chosen before N control all actual mask '
    'short-cube dimensions. Combining this with the original detection estimate '
    'controls the actual original subset correlation with a tracked F-S target; '
    'neither target-cube smallness nor correlation smallness is assumed.',
    'The mask-generated master catalogue is exactly independent of later gap metadata, '
    'even across different master counts. At a fixed master count the actual master '
    'family is exactly independent of that metadata as well. Selecting principal and '
    'padding indices therefore does not change the master data used to select models.',
    'On an actual selected chain, exact principal-pivot recovery and the actual common '
    'fine padding transport the retained original master short-cube bounds to the '
    'actual endpoint cubes and subset correlation. The same integer functions, '
    'catalogue, harmonic law and quotient scale are retained throughout.',
    'Given the displayed interval inverse existence inputs, one actual finite family '
    'of native coarse models now controls F-S in the actual original subset correlation '
    'for every selected chain and every mask support. J, the positive accuracies and '
    'the required master count precede arithmetic data and inputs. The same models '
    'retain their coarse projection approximation, global [0,1] bounds, one common '
    'native nilmanifold and uniform observable bounds. This is an actual selected '
    'F-S prediction component, not a proof of inverse existence or the full '
    'coloring-derived Prediction Principle.'
]
reviews = [
    'PROGRESS. The preceding original short-cube sampling round was terminal-successfully '
    'rechecked and its authoritative manifest copied before edits. Retained proof-source '
    'hashes and selected transitive axiom sets remain unchanged except root and registry.',
    'The exact conditional pushforward identity retains the original event denominator. '
    'Under a bijective variable renaming, global injectivity is equivalent to local '
    'injectivity and polynomial evaluation commutes with rename. The statistic proof '
    'first abstracts its natural polynomial step, which also controls the dependent '
    'finite direction type; it then applies congruence to the exact evaluation identity. '
    'No implicit replacement of the direction length is used.',
    'The actual fullMaskRowStage prime-arity theorem gives equality with maskMasterArity '
    'for every target. The generated slot map is definitionally finCongr of this '
    'equality. Exact prime-coordinate reindexing therefore gives the actual local '
    'prime-good mean from the renamed master mean. Polynomial nonzeroness and '
    'denominator membership follow from the retained actual row catalogue.',
    'The finite cube-order list is Fin(maskRowCountBound+1), fixed before all later '
    'master data. The retained finite-order inverse implication supplies the same J '
    'and threshold for this whole list. Every actual target dimension selects an '
    'element by its proved bound. Its renamed polynomial belongs to the actual '
    'master catalogue and its renamed test family is nonzero, so the original '
    'projection-to-short-cube theorem applies to the actual difference f-model.',
    'The original detection tolerance is chosen before N. The actual local short-cube '
    'mean is identified with the proved master mean, and the actual conditioning '
    'and detection theorems give the original subset-correlation bound. Later chain '
    'parameters and admissible companion functions can affect the eventual stage, '
    'but cannot affect J or the positive threshold.',
    'Master catalogue and fixed-count master family gap independence are proved by '
    'definitional equality: actual row coefficients, slots and catalogue construction '
    'do not inspect the metadata gap field. This removes circular dependence of the '
    'master on subsequently selected fine padding indices.',
    'The selected-chain transfer preserves the exact first selected padding index, '
    'actual pivot, original polynomial step, original prime law and same F-S integer '
    'function. The actual chain allocation bounds supply master-range, gap-order '
    'and tail hypotheses. The original atTop estimates are transferred to the same '
    'tail-containing ultrafilter. Its short-cube input is supplied in the final '
    'application by the retained proved finite-order native chain-model theorem.',
    'The final application selects the analytic error from the actual detection '
    'tolerance before selecting N. It uses the same finite model family for every '
    'chain, preserves every coarse approximation and unit bound, and retains the '
    'common native manifold with fixed observable bounds. The first combined '
    'proof exceeded the existing per-declaration heartbeat budget; factoring '
    'integer sampling transfer from native-model application resolved this with '
    'the original statement scope and unchanged default resources.',
    'Seven modules add fourteen theorems, all selected for transitive kernel audit. '
    'All final focused compilations, the complete build and selected kernel audit '
    'are warning-free and terminal-successful. No new definitions, instances, '
    'resource options or forbidden proof steps are introduced.',
    'The finite-list interval inverse existence proposition remains explicitly '
    'unproved. The actual F-S component is now integrated, but coloring-derived '
    'rho-F testing and the full Prediction Principle still require their complete '
    'integration. Calibration/Alignment and final ordered rapidly separated '
    'monochromatic extraction remain incomplete. StrongConjecture remains '
    'unproved. No unavoidable blocker is established; no completed public '
    'prize submission is claimed.'
]
source = Path(previous + '-audit.py').read_text(encoding='utf-8')
remaining = ast.literal_eval(re.search(r'^REMAINING = (.+)$', source, re.M).group(1))
marker = 'The finite-list interval inverse existence statement itself'
assert marker in remaining
remaining = remaining.replace(marker, ' '.join(components) + ' ' + marker, 1)
source = source.replace("PREFIX = '" + previous + "'", "PREFIX = '" + prefix + "'")
source = source.replace("OLD = 'round-mask-uniform-detection'", "OLD = '" + previous + "'")
for name, value in [('MODULES', modules), ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^' + name + r' = .+$', name + ' = ' + repr(value), source, count=1, flags=re.M)
numbers = {'1206': '1211', '1211': '1218', '1193': '1200', '1202': '1209', '5459': '5473'}
source = re.sub(r'\b(?:1206|1211|1193|1202|5459)\b', lambda m: numbers[m.group()], source)
source = source.replace('== 15\n', '== 14\n')
source = source.replace("'theorem_count': 15, 'selected_report_count': 15", "'theorem_count': 14, 'selected_report_count': 14")
source = source.replace('new_theorems=15', 'new_theorems=14')
source = source.replace('new_axiom_reports=15', 'new_axiom_reports=14')
source = source.replace('new_module_count=5, new_theorem_count=15', 'new_module_count=7, new_theorem_count=14')
source = source.replace('new_selected_report_count=15', 'new_selected_report_count=14')
source = source.replace("('Hindman168.FiniteMass.' if p.endswith('FiniteConditionedSubsetBound.lean') else 'Hindman168.')",
                        "'Hindman168.'")
source = re.sub(r'application_review=\[.*?\], new_modules=MODULES',
                'application_review=' + repr(reviews) + ', new_modules=MODULES', source, count=1, flags=re.S)
source = source.replace('05_prediction: exact original short-cube sampling and local conditioned-law detection of subset correlation',
                        '05_prediction: exact mask prime-slot transport and actual selected native F-S subset correlations')
source = source.replace('Register and audit the original short-cube sampling and conditioning bridge.',
                        'Register and audit the actual selected native mask-correlation bridge.')
ast.parse(source)
Path(prefix + '-audit.py').write_text(source, encoding='utf-8')
print(json.dumps({'modules': modules, 'theorems': 14, 'definitions': 0, 'reports': 14}))
