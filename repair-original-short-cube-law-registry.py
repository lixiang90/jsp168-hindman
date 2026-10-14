from pathlib import Path
import json

path = Path('round-original-short-cube-law-registration.json')
record = json.loads(path.read_text(encoding='utf-8'))
repairs = {
    'Hindman168.conditioned_subset_expectation_bound':
        'Hindman168.FiniteMass.conditioned_subset_expectation_bound',
    'Hindman168.conditioned_subset_expectation_le_twice':
        'Hindman168.FiniteMass.conditioned_subset_expectation_le_twice',
}
for old in repairs:
    assert record['names'].count(old) == 1
record['names'] = [repairs.get(name, name) for name in record['names']]
path.write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
print(json.dumps({'corrected_namespace_names': list(repairs.values())}))
