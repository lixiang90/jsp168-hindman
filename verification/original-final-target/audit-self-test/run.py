#!/usr/bin/env python3
"""Explicit isolated audit-mechanism self-test; does not import the JSP target.

--output-dir must select a new directory under verification-local. Only tiny
fixtures are compiled with the installed pinned Lean; Lake is never invoked.
The deliberately unapproved test axioms are outside the proof source closure.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output-dir', required=True, help='New directory below verification-local')
args = parser.parse_args()
output = Path(args.output_dir)
if not output.is_absolute():
    output = ROOT / output
output = output.resolve()
if not output.is_relative_to(ROOT / 'verification-local') or output == ROOT / 'verification-local':
    raise ValueError('Self-test output must stay below verification-local')
if output.exists():
    raise ValueError('Output exists; choose a fresh self-test directory')

toolchain = (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip()
if toolchain != 'leanprover/lean4:v4.32.2':
    raise ValueError('Pinned toolchain changed')
toolchain_dir = Path(os.environ.get('ELAN_HOME', str(Path.home() / '.elan'))) / 'toolchains' / toolchain.replace('/', '--').replace(':', '---')
lean = toolchain_dir / 'bin' / ('lean.exe' if os.name == 'nt' else 'lean')
if not lean.is_file():
    raise FileNotFoundError('Install the pinned Lean toolchain before this explicit self-test')

generator_path = HERE.parent / 'prepare.py'
generator = runpy.run_path(str(generator_path))
# Reuse the exact real audit generator. Only import/target module names change.
audit = generator['audit_source'](['Hindman168.JSP000168'])
if audit.count('Hindman168.JSP000168') != 2:
    raise ValueError('Unexpected audit generator shape; review the fixture adaptation')
audit = audit.replace('Hindman168.JSP000168', 'ProbeModule')
output.mkdir(parents=True, exist_ok=False)
fixtures = ['ProbeModule.lean', 'ProbeAudit.lean', 'ProbeEndpoint.lean']
for name in fixtures:
    shutil.copyfile(HERE / name, output / name)
(output / 'ProbeExactAudit.lean').write_text(audit, encoding='utf-8')

sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
env = {**os.environ, 'LEAN_PATH': str(output), 'LEAN_NUM_THREADS': '1'}
report = {
    'schema': 'hindman.audit-mechanism-self-test.v1',
    'started_utc': datetime.now(timezone.utc).isoformat(),
    'toolchain': toolchain, 'status': 'running',
    'scope': 'Isolated tiny audit-mechanism fixtures only; deliberate private test axioms are not in the proof source closure.',
    'target_imported': False, 'lake_executed': False,
    'actual_final_target_verification_executed': False,
    'output_directory': output.relative_to(ROOT).as_posix(),
    'canonical_generator_sha256': sha(generator_path),
    'self_test_source_sha256': {p.relative_to(ROOT).as_posix(): sha(p)
                               for p in [HERE / 'run.py', *[HERE / name for name in fixtures]]},
    'generated_exact_audit_sha256': sha(output / 'ProbeExactAudit.lean'),
    'runs': [],
}
def save():
    (output / 'report.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n', encoding='utf-8', newline='\n')

save()
try:
    for name, extra, expected in [
        ('ProbeModule.lean', ['-o', 'ProbeModule.olean'], 0),
        ('ProbeAudit.lean', [], 0),
        ('ProbeEndpoint.lean', [], 0),
        ('ProbeExactAudit.lean', [], 1),
    ]:
        argv = ['-j1', '--trust=0', '-DautoImplicit=false', *extra, name]
        run = subprocess.run([str(lean), *argv], cwd=output, env=env,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True, encoding='utf-8')
        passed = run.returncode == expected
        if name == 'ProbeExactAudit.lean':
            passed = passed and 'Unexpected axiom' in run.stdout and '_private.ProbeModule.' in run.stdout and 'hiddenUnusedAxiom' in run.stdout
        report['runs'].append({'fixture': name, 'arguments': argv,
                               'exit_code': run.returncode, 'expected_exit_code': expected,
                               'expected_result_observed': passed,
                               'stdout': run.stdout, 'stderr': run.stderr})
        save()
        if not passed:
            raise RuntimeError('Unexpected fixture result: ' + name)
    report['fixture_artifact_sha256'] = {p.name: sha(p) for p in sorted(output.glob('ProbeModule.olean*'))}
    report['status'] = 'audit mechanism self-test passed; actual JSP target not executed'
except Exception as error:
    report['status'] = 'failed'
    report['error'] = str(error)
finally:
    report['finished_utc'] = datetime.now(timezone.utc).isoformat()
    save()
print(json.dumps({'report': (output / 'report.json').relative_to(ROOT).as_posix(),
                  'report_sha256': sha(output / 'report.json'), 'status': report['status']}, indent=2))
raise SystemExit(1 if report['status'] == 'failed' else 0)
