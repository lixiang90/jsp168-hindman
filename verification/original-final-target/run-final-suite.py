"""Record the final checks, real exits, and unchanged inputs around the suite."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
manifest_path = ROOT / sys.argv[1]
output = ROOT / 'verification-local' / sys.argv[2]
output.mkdir(exist_ok=False)
manifest = json.loads(manifest_path.read_bytes())
audit = manifest_path.parent / 'CheckAllDeclarations.lean'
commands = [
    ['lake', 'env', 'lean', '-j1', '--trust=0', '-DautoImplicit=false',
     'verification/original-final-target/CheckEndpoint.lean'],
    ['lake', 'env', 'lean', '-j1', '--trust=0', '-DautoImplicit=false',
     audit.relative_to(ROOT).as_posix()],
    ['lake', 'env', 'leanchecker', '--fresh', '--verbose', 'Hindman168.JSP000168'],
]


def now():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def write(name, value):
    (output / name).write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')


def check_sources():
    expected = {entry['path']: entry['sha256'] for entry in manifest['sources'].values()}
    expected.update(manifest['repository_input_sha256'])
    expected[audit.relative_to(ROOT).as_posix()] = manifest['all_declarations_audit_source_sha256']
    failures = [name for name, digest in expected.items()
                if not (ROOT / name).is_file() or sha(ROOT / name) != digest]
    return {'checked_utc': now(), 'files': len(expected), 'mismatches': failures,
            'passed': not failures}


def check_environment():
    version = subprocess.check_output(['lake', 'env', 'lean', '--version'],
                                      cwd=ROOT, text=True).strip()
    prefix = Path(subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'],
                                         cwd=ROOT, text=True).strip())
    binaries = {path.name: sha(path) for path in sorted((prefix / 'bin').iterdir())
                if path.is_file() and (path.suffix == '.dll' or
                                       path.name in {'lean.exe', 'lake.exe', 'leanchecker.exe'})}
    packages = []
    for package in json.loads((ROOT / 'lake-manifest.json').read_bytes())['packages']:
        path = ROOT / '.lake/packages' / package['name']
        head = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'],
                                       cwd=ROOT, text=True).strip()
        dirty = subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain',
                                         '--untracked-files=no'], cwd=ROOT, text=True).strip()
        packages.append({'name': package['name'], 'pinned': package['rev'], 'head': head,
                         'tracked_status': dirty})
    return {'lean_version': version, 'toolchain_binary_sha256': binaries, 'packages': packages,
            'passed': 'version 4.32.2,' in version and all(
                p['pinned'] == p['head'] and not p['tracked_status'] for p in packages)}


def artifacts():
    prefix = Path(subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'],
                                         cwd=ROOT, text=True).strip())
    roots = [('.lake/build/lib/lean', ROOT / '.lake/build/lib/lean'),
             ('<pinned-toolchain>/lib/lean', prefix / 'lib/lean')]
    roots.extend((p.relative_to(ROOT).as_posix(), p)
                 for p in sorted((ROOT / '.lake/packages').glob('*/.lake/build/lib/lean')))
    result = {}
    for label, root in roots:
        for path in sorted(root.rglob('*.olean*')):
            if path.is_file() and path.name.endswith(('.olean', '.olean.private', '.olean.server')):
                name = label + '/' + path.relative_to(root).as_posix()
                result[name] = {'bytes': path.stat().st_size, 'sha256': sha(path)}
    for module in manifest['sources']:
        name = '.lake/build/lib/lean/' + module.replace('.', '/') + '.olean'
        if name not in result:
            raise RuntimeError('Missing final closure artifact: ' + name)
    return result


record = {'target': 'Hindman168.JSP000168', 'started_utc': now(), 'status': 'running',
          'manifest': manifest_path.relative_to(ROOT).as_posix(),
          'manifest_sha256': sha(manifest_path), 'commands': [],
          'lean_num_threads': '1', 'whole_suite_exit_code': None}
write('result.json', record)
try:
    record['sources_before'] = check_sources()
    record['environment_before'] = check_environment()
    write('result.json', record)
    if not record['sources_before']['passed'] or not record['environment_before']['passed']:
        raise RuntimeError('Source or environment inputs differ from the selected pins')
    print('Hashing proof artifacts before checks', flush=True)
    before = artifacts()
    write('artifacts-before.json', before)
    record['artifacts_before_sha256'] = sha(output / 'artifacts-before.json')
    record['artifact_files'] = len(before)
    write('result.json', record)
    env = {**os.environ, 'LEAN_NUM_THREADS': '1'}
    for index, command in enumerate(commands, 1):
        entry = {'command': command, 'started_utc': now(), 'status': 'running', 'exit_code': None,
                 'log': f'{index:02d}.log'}
        record['commands'].append(entry)
        write('result.json', record)
        print(f'Starting check {index}/3: {command[2]}', flush=True)
        with (output / entry['log']).open('wb') as stream:
            process = subprocess.run(command, cwd=ROOT, env=env, stdout=stream,
                                     stderr=subprocess.STDOUT)
        entry.update(exit_code=process.returncode, finished_utc=now(),
                     status='passed' if process.returncode == 0 else 'failed')
        write('result.json', record)
        print(f'Check {index} exit: {process.returncode}', flush=True)
        if process.returncode != 0:
            raise RuntimeError(f'Check {index} failed; see its unmodified log')
    record['sources_after'] = check_sources()
    record['environment_after'] = check_environment()
    print('Hashing proof artifacts after checks', flush=True)
    after = artifacts()
    write('artifacts-after.json', after)
    record['artifacts_after_sha256'] = sha(output / 'artifacts-after.json')
    record['changed_artifacts'] = [p for p in sorted(before.keys() | after.keys())
                                    if before.get(p) != after.get(p)]
    if (not record['sources_after']['passed'] or record['changed_artifacts'] or
            record['environment_before'] != record['environment_after']):
        raise RuntimeError('Proof inputs changed during verification')
    record.update(status='passed', whole_suite_exit_code=0, finished_utc=now())
except Exception as error:
    record.update(status='failed', error=str(error), whole_suite_exit_code=1, finished_utc=now())
write('result.json', record)
print('Whole suite status: ' + record['status'], flush=True)
raise SystemExit(record['whole_suite_exit_code'])
