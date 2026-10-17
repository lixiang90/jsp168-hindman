"""Record a complete command exit without treating partial build progress as success."""
from pathlib import Path
from datetime import datetime, timezone
import json
import hashlib
import os
import runpy
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
stage = sys.argv[1]
targets_file = root / sys.argv[2]
targets = targets_file.read_text(encoding='utf-8').split()
assert targets and all(m.startswith(('OAI.', 'Hindman168.')) for m in targets)
folder = root / 'verification-local' / stage
folder.mkdir(exist_ok=False)
command = ['lake', '-v', 'build', *targets]
threads = os.environ.get('HINDMAN_BUILD_THREADS', '4')
record = {'command': command, 'started_utc': datetime.now(timezone.utc).isoformat(),
          'status': 'running', 'exit_code': None, 'lean_num_threads': threads}
result_path = folder / 'result.json'
result_path.write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
record['runner_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def snapshot(name):
    # This inventories source/tool bytes without invoking Lean or Lake.
    report = runpy.run_path(str(root / 'verification/original-final-target/prepare.py'))['inventory']()[0]
    data = (json.dumps(report, indent=2, ensure_ascii=True)+'\n').encode('utf-8')
    path = folder / name
    path.write_bytes(data)
    record[name.replace('.json', '').replace('-', '_') + '_sha256'] = hashlib.sha256(data).hexdigest()
    return report


try:
    before = snapshot('sources-before.json')
    result_path.write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
    print('Building '+str(len(targets))+' targets; log: '+str(folder / 'build.log'), flush=True)
    env = {**os.environ, 'LEAN_NUM_THREADS': threads}
    with (folder / 'build.log').open('wb') as log:
        process = subprocess.run(command, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT)
    record.update(exit_code=process.returncode,
                  finished_utc=datetime.now(timezone.utc).isoformat())
    record['build_log_sha256'] = hashlib.sha256((folder / 'build.log').read_bytes()).hexdigest()
    after = snapshot('sources-after.json')
    record['source_inputs_unchanged'] = before == after
    record['binding_finished_utc'] = datetime.now(timezone.utc).isoformat()
    record['status'] = 'passed' if process.returncode == 0 and before == after else 'failed'
    record['wrapper_exit_code'] = 0 if record['status'] == 'passed' else 1
except Exception as error:
    record.update(status='failed', wrapper_exit_code=1,
                  binding_error=str(error), binding_finished_utc=datetime.now(timezone.utc).isoformat())
result_path.write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
print('Whole build exit: '+str(record['exit_code'])+'; bound wrapper exit: '+str(record['wrapper_exit_code']), flush=True)
raise SystemExit(record['wrapper_exit_code'])
