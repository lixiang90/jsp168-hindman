from pathlib import Path
import json

def read_json(name):
    return json.loads(Path(name).read_text(encoding='utf-8'))

path = Path('CONTINUATION.txt')
text = path.read_text(encoding='utf-8')
text = text.replace('Current batch: round-rough-labelled-native-tests',
                    'Earlier batch: round-rough-labelled-native-tests')
for prefix in ['round-rough-native-piece-descent', 'round-rough-native-bad-family']:
    review = read_json(prefix+'-review.json')
    stats = review['verified']
    marker = ('Current batch: ' if prefix.endswith('bad-family') else 'Earlier batch: ')+prefix
    assert marker not in text
    text += ('\n\n'+marker+', verified 2026-10-11. '+str(len(review['new_modules']))+
             ' modules, '+str(stats['new_theorems'])+' theorems, '+
             str(stats['new_definitions'])+' definitions; full build '+str(stats['build_jobs'])+
             ' jobs; '+str(stats['project_modules'])+' project modules; '+
             str(stats['selected_axiom_reports'])+' selected transitive axiom reports. '+
             'Retained proof sources and axiom sets unchanged; standard axioms only; '+
             'all six pinned paper sections matched. Author-side verification, not independent kernel replay.\n')
    for item in review['application_review']:
        text += '- '+item+'\n'
text += '''
Immediate next work: connect rough_piece_descent_thresholds to all integer original-box side hypotheses and the positive fixed discrepancy gap used in rough_native_model_bad_family. Derive coprimality with the fixed rational period from original primorial roughness once w is large. Apply actual affine coefficient-obstruction interpolation and constant-term fractional-part thinning uniformly along source bad families, preserving their common polynomial and fixed degree. Combine the resulting finite smaller families with rough_native_fixed_bad_quotient_subsequences; this latter theorem explicitly uses actual length restriction and transports Scale divergence as well as PowerDominates. Do not assume a common quotient alone produces a scale subsequence at each length. The quantitative Leibman input still has to be proved, including the corrected arbitrary-box coefficient comparison, stretched-filtration hypotheses and uniform finite nonzero character list. The new native family interfaces use real observables; retain an explicit complex-to-real discrepancy reduction before claiming the paper's complex-observable proposition.
'''
text += '\nRemaining: '+read_json('round-rough-native-bad-family-review.json')['remaining']+'\n'
path.write_text(text, encoding='utf-8')
print('Updated continuation for both audited batches.')
