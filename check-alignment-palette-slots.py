from pathlib import Path
import ast
import hashlib
import json
import subprocess
import time

prefix = 'round-alignment-palette-slots'
source = Path(prefix + '-audit.py').read_text(encoding='utf-8')
modules = next(ast.literal_eval(n.value) for n in ast.parse(source).body
    if isinstance(n, ast.Assign) and isinstance(n.targets[0], ast.Name)
    and n.targets[0].id == 'MODULES')
results = []
previous_path = Path(prefix + '-focused-results.json')
previous = {r['module']: r for r in json.loads(previous_path.read_text(encoding='utf-8'))} \
    if previous_path.exists() else {}
for module in modules:
    retained = previous.get(module)
    if retained and retained['source_sha256'] == hashlib.sha256(Path(module).read_bytes()).hexdigest():
        assert retained['terminal'] and retained['exit_code'] == 0
        assert not Path(retained['log']).read_bytes().strip()
        assert retained['log_sha256'] == hashlib.sha256(Path(retained['log']).read_bytes()).hexdigest()
        results.append(retained)
        print(json.dumps({'retained_focused_result': module}), flush=True)
        continue
    start = time.monotonic()
    command = ['lake', 'env', 'lean', '-DautoImplicit=false', module]
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = prefix + '-focused-' + Path(module).stem + '.txt'
    Path(log).write_bytes(result.stdout)
    entry = dict(module=module, command=command, terminal=True, exit_code=result.returncode,
        elapsed_seconds=time.monotonic()-start,
        source_sha256=hashlib.sha256(Path(module).read_bytes()).hexdigest(),
        log=log, log_sha256=hashlib.sha256(result.stdout).hexdigest())
    results.append(entry)
    print(json.dumps(entry), flush=True)
    assert result.returncode == 0 and not result.stdout.strip(), result.stdout.decode('utf-8')
Path(prefix + '-focused-results.json').write_text(json.dumps(results, indent=2), encoding='utf-8')
