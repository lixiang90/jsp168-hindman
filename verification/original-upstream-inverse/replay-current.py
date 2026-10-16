#!/usr/bin/env python3
"""Check committed source hashes, or explicitly replay exactly the current 751 targets.

Default is read-only: python3 verification/original-upstream-inverse/replay-current.py
Use --run to build/audit later; requires this repository's pinned Lake/toolchain.
No temporary recovery directory, upstream clone, network evidence service, or old
binary is needed for the static check. Dependencies must be installed for --run.
The preserved 1042-module manifest remains historical evidence, not a new replay.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(test, message):
    if not test:
        raise RuntimeError(message)


def audit_source(modules):
    modules = sorted(modules)
    return ('\n'.join('import ' + m for m in modules) + '\nimport Lean\n\nopen Lean Elab Command\n'
        'set_option maxRecDepth 10000\nset_option maxHeartbeats 0\n\nrun_cmd do\n  let env ← getEnv\n'
        '  let targets : List Name := [' + ','.join('`' + m for m in modules) + ']\n'
        '  let mut seen : Std.HashSet Name := {}\n  let mut entries : Nat := 0\n  let mut modules : Nat := 0\n'
        '  for i in [:env.header.moduleNames.size] do\n    if targets.contains env.header.moduleNames[i]! then\n'
        '      modules := modules + 1\n      for name in env.header.moduleData[i]!.constNames do\n'
        '        entries := entries + 1\n        unless seen.contains name do\n          seen := seen.insert name\n'
        '          let axioms ← collectAxioms name\n          for ax in axioms do\n'
        '            unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do\n'
        '              throwError m!"Unexpected axiom {ax} in {name}"\n'
        '  unless modules == targets.length && seen.size > 0 do\n'
        '    throwError "Missing target module or empty audit"\n'
        '  logInfo m!"AUDIT COMPLETE: {modules} modules; {seen.size} unique declarations; {entries} records; only standard axioms"\n')


def check(manifest):
    require(sha(Path(__file__).read_bytes()) == manifest['reproduction_script_sha256'], 'Replay script changed')
    history_file = ROOT / manifest['historical_base']['path']
    require(sha(history_file.read_bytes()) == manifest['historical_base']['sha256'], 'Historical manifest changed')
    prior = json.loads(history_file.read_bytes())['source_modules']
    additions = manifest['new_sources']
    require(not prior.keys() & additions.keys(), 'Increment unexpectedly replaces a historical module')
    combined = {**prior, **additions}
    require(len(prior) == 1042 and len(additions) == 15 and len(combined) == 1057, 'Wrong source partition')
    for module, entry in combined.items():
        expected_path = 'dependencies/openai-finite-szemeredi/' + module.replace('.', '/') + '.lean'
        require(entry['path'] == expected_path, 'Unexpected module path: ' + module)
        require(sha((ROOT / entry['path']).read_bytes()) == entry['sha256'], 'Source changed: ' + module)
        require(set(entry['oai_imports']) <= combined.keys(), 'Unclosed composed imports: ' + module)
    targets = manifest['current_replay_modules']
    require(targets == sorted(set(targets)) and len(targets) == 751, 'Invalid current replay target list')
    require(set(targets) <= combined.keys(), 'Unknown replay target')
    require(len(set(targets) & prior.keys()) == 736, 'Wrong historical overlap')
    for module in targets:
        require(set(combined[module]['oai_imports']) <= set(targets), 'Unclosed current imports: ' + module)
    for path, digest in manifest['repository_input_sha256'].items():
        require(sha((ROOT / path).read_bytes()) == digest, 'Pinned input changed: ' + path)
    generated = audit_source(targets)
    require(sha(generated.encode()) == manifest['current_verification']['audit_source_sha256'], 'Audit source changed')
    return targets, generated


def artifact_hashes(targets):
    result = {}
    for module in targets:
        relative = module.replace('.', '/')
        required = ROOT / '.lake/build/lib/lean' / (relative + '.olean')
        require(required.is_file(), 'Missing freshly built artifact: ' + module)
        for folder, suffixes in [('lib/lean', ['olean', 'ilean', 'olean.server', 'olean.private', 'ir']),
                                 ('ir', ['c', 'bc'])]:
            for suffix in suffixes:
                path = ROOT / '.lake/build' / folder / (relative + '.' + suffix)
                if path.is_file():
                    result[str(path.relative_to(ROOT))] = sha(path.read_bytes())
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run', action='store_true', help='explicitly execute the pinned 751-target build and trust=0 audit')
    args = p.parse_args()
    manifest = json.loads((HERE / 'current-replay.json').read_bytes())
    targets, generated = check(manifest)
    print('Source check passed: 1057 composed modules = 1042 historical + 15 additions; current targets: 751.', flush=True)
    if not args.run:
        print('No Lean or Lake executed. Use --run for a new replay of exactly the 751 current targets.')
        return
    env = {**os.environ, 'LEAN_NUM_THREADS': '1'}
    with tempfile.TemporaryDirectory(prefix='hindman-current-replay-') as work:
        audit = Path(work) / 'CheckAxioms.lean'
        audit.write_text(generated, encoding='utf-8')
        subprocess.run(['lake', 'build', *targets], cwd=ROOT, env=env, check=True)
        check(manifest)
        before = artifact_hashes(targets)
        subprocess.run(['lake', 'env', 'lean', '-j1', '--trust=0', '-DautoImplicit=false', str(audit)], cwd=ROOT, env=env, check=True)
        check(manifest)
        require(artifact_hashes(targets) == before, 'Artifacts changed across the audit')
    print('New 751-target replay completed; sources/artifacts stable across audit. Historical-only 306 were not audit targets.')


if __name__ == '__main__':
    main()
