from pathlib import Path
import json
import importlib.util

spec = importlib.util.spec_from_file_location('current_audit', 'round-bounded-count-sampling-audit.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
path = Path('round-bounded-count-sampling-registration.json')
record = json.loads(path.read_text(encoding='utf-8'))
old_name = 'Hindman168.expectation_piMass_density'
new_name = 'Hindman168.FiniteMass.expectation_piMass_density'
assert record['names'].count(old_name) == 1
assert new_name not in record['names']
record['names'] = [new_name if n == old_name else n for n in record['names']]
record['declarations'] = audit.declarations()
assert record['names'] == ['Hindman168.' + n for p, ds in audit.declarations().items() for _, n in ds]
registry = Path('Verification.lean').read_text(encoding='utf-8')
assert registry.splitlines().count('#print axioms ' + old_name) == 1
assert '#print axioms ' + new_name not in registry.splitlines()
Path('Verification.lean').write_text(registry.replace('#print axioms ' + old_name,
    '#print axioms ' + new_name, 1), encoding='utf-8')
path.write_text(json.dumps(record, indent=2), encoding='utf-8')
print('Corrected only the fully qualified kernel report name; proof sources unchanged.')
