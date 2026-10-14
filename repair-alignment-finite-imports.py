from pathlib import Path
import json

prefix = 'round-alignment-finite-alternatives'
registration = json.loads(Path(prefix + '-registration.json').read_text(encoding='utf-8'))
root = Path('Hindman168.lean')
source = root.read_text(encoding='utf-8')
for path in registration['modules']:
    bad = 'import ' + path[:-7].replace('/', '.')
    correct = 'import ' + path[:-5].replace('/', '.')
    assert source.splitlines().count(bad) == 1
    assert correct not in source.splitlines()
    source = source.replace(bad + '\n', correct + '\n', 1)
root.write_text(source, encoding='utf-8')
print(json.dumps({'repaired_root_imports': len(registration['modules'])}))
