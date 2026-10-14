from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import time

prefix = 'round-calibration-tolerance-cap'
modules = [
    'FiniteOrderNativeShortCubeModelsCapped', 'FiniteOrderNativeChainPredictionCapped',
    'SelectedNativeMaskCorrelationCapped', 'SelectedColorDenseNativeModelsCapped',
    'SelectedColorNativeTestingModelsCapped', 'SelectedColorCalibratedModelsCapped',
    'SelectedColorCalibrationTolerance']
records = []
sys.stdout.reconfigure(encoding='utf-8')

def run(command, module, kind):
    path = Path(prefix+'-'+module+'-'+kind+'.txt')
    start = time.monotonic()
    with path.open('wb') as stream:
        result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    record = dict(module=module, kind=kind, command=command, terminal=True,
        exit_code=result.returncode, elapsed_seconds=time.monotonic()-start,
        log_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    records.append(record)
    Path(prefix+'-focused-chain.json').write_text(json.dumps(records, indent=2), encoding='utf-8')
    print(json.dumps(record), flush=True)
    output = path.read_text(encoding='utf-8')
    if result.returncode or re.search(r'(?:error:|warning:)', output):
        print(output, flush=True)
        sys.exit(result.returncode or 1)

# The first focused check has already passed; build it for its dependent.
run(['lake', 'build', 'Hindman168.'+modules[0]], modules[0], 'dependency')
for index, module in enumerate(modules[1:], 1):
    run(['lake', 'env', 'lean', '-DautoImplicit=false', 'Hindman168/'+module+'.lean'], module, 'focused')
    if index < len(modules)-1:
        run(['lake', 'build', 'Hindman168.'+module], module, 'dependency')
