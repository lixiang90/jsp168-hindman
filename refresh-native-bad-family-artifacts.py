import importlib.util
from pathlib import Path

spec = importlib.util.spec_from_file_location('audit', 'round-rough-native-bad-family-audit.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
results = []
for p in audit.MODULES:
    target = Path('.lake/build/lib/lean')/Path(p).with_suffix('.olean')
    if target.stat().st_mtime_ns >= Path(p).stat().st_mtime_ns:
        continue
    result = audit.run(['lake', 'env', 'lean', '-DautoImplicit=false', '-o',
        str(target), p], audit.PREFIX+'-'+Path(p).stem+'-artifact-refresh.txt')
    result.update(module=p, source_sha256=audit.digest(p), olean_sha256=audit.digest(target))
    results.append(result)
    print('Refreshed compiled artifact '+p, flush=True)
audit.write(audit.PREFIX+'-artifact-refresh-results.json', results)
