#!/usr/bin/env python3
"""Inventory the actual final target's local source closure; never execute Lean.

Default is read-only. --output-dir DIR explicitly writes prepared source hashes,
the complete local module list, and an all-declaration axiom-audit Lean source.
Only Hindman168, OAI and PrimeNumberTheoremAnd are traversed. Other imports are
reported as external boundaries, without claiming their source verification.
"""

import argparse
from collections import Counter, defaultdict
import hashlib
import heapq
import json
from pathlib import Path
import re
import runpy
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TARGET = 'Hindman168.JSP000168'
NAMESPACES = {'Hindman168', 'OAI', 'PrimeNumberTheoremAnd'}
MODULE_RE = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')
HELPER_PATH = ROOT / 'verification/original-upstream-inverse/verify-prepared.py'
HELPERS = runpy.run_path(str(HELPER_PATH))
require, repo_path, lean_code = (HELPERS[name] for name in ('require', 'repo_path', 'lean_code'))


def sha(data):
    return hashlib.sha256(data).hexdigest()


def source_path(module):
    require(MODULE_RE.fullmatch(module) and module.split('.')[0] in NAMESPACES,
            'Invalid local module: ' + module)
    prefix = 'dependencies/openai-finite-szemeredi/' if module.split('.')[0] == 'OAI' else ''
    return repo_path(prefix + module.replace('.', '/') + '.lean', manifest=True)


def imports(text):
    result = []
    for line in lean_code(text).splitlines():
        match = re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(?:(?:all|meta)\s+)?(.*)$', line)
        if match:
            modules = match[1].split()
            require(modules and all(MODULE_RE.fullmatch(module) for module in modules),
                    'Unsupported import syntax: ' + line.strip())
            result.extend(modules)
    return result


def audit_source(modules):
    modules = sorted(modules)
    for module in modules:
        source_path(module)
    chunks = [modules[i:i+128] for i in range(0, len(modules), 128)]
    chunk_names = [f'auditTargetChunk{i:03d}' for i in range(len(chunks))]
    target_definitions = '\n'.join(
        '@[noinline] private def ' + name + ' : Array Name := #['
        + ', '.join('`' + module for module in chunk) + ']\n'
        for name, chunk in zip(chunk_names, chunks))
    target_chunks = '#[' + ', '.join(chunk_names) + ']'
    return ('/- PREPARED: every declaration of the listed local target closure; not executed. -/\n'
        + '\n'.join('import ' + module for module in modules)
        + '\nimport Lean\n\nopen Lean Elab Command\n'
        + 'set_option maxRecDepth 10000\nset_option maxHeartbeats 0\n\n'
        + target_definitions + '\nrun_cmd do\n'
        + '  let env ← getEnv\n  let targets : Array Name := ('
        + target_chunks + ' : Array (Array Name)).flatten\n'
        + '  let mut found : Std.HashSet Name := {}\n'
        + '  let mut seen : Std.HashSet Name := {}\n  let mut records : Nat := 0\n'
        + '  for i in [:env.header.moduleNames.size] do\n'
        + '    let moduleName := env.header.moduleNames[i]!\n'
        + '    if targets.contains moduleName then\n'
        + '      found := found.insert moduleName\n      let mut count : Nat := 0\n'
        + '      for name in env.header.moduleData[i]!.constNames do\n'
        + '        count := count + 1\n        records := records + 1\n'
        + '        seen := seen.insert name\n        let axioms ← collectAxioms name\n'
        + '        for ax in axioms do\n'
        + '          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do\n'
        + '            throwError m!"Unexpected axiom {ax} in {moduleName}: {name}"\n'
        + '        logInfo m!"AUDIT DECL: {moduleName}; {name}; axioms: {axioms}"\n'
        + '      logInfo m!"AUDIT MODULE: {moduleName}; all {count} declaration records checked"\n'
        + '  for target in targets do\n    unless found.contains target do\n'
        + '      throwError m!"Missing target module: {target}"\n'
        + '  unless seen.size > 0 do\n    throwError "Empty declaration audit"\n'
        + '  logInfo m!"AUDIT COMPLETE: {found.size} local modules; {seen.size} unique declarations; {records} records; only standard three axioms"\n')


def inventory():
    toolchain = (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip()
    require(toolchain == 'leanprover/lean4:v4.32.2', 'Pinned Lean toolchain changed')
    lockfile = json.loads((ROOT / 'lake-manifest.json').read_bytes())
    mathlib = [package for package in lockfile['packages'] if package['name'] == 'mathlib']
    require(len(mathlib) == 1 and mathlib[0]['rev']
            == '905b95818eb32af7874a58b427f50c1711a5e96c', 'Pinned mathlib changed')
    sources, external, pending = {}, defaultdict(set), [TARGET]
    while pending:
        module = pending.pop()
        if module in sources:
            continue
        path = source_path(module)
        require(path.is_file(), 'Missing local import: ' + module)
        data = path.read_bytes()
        direct = imports(data.decode('utf-8'))
        local = sorted({name for name in direct if name.split('.')[0] in NAMESPACES})
        boundary = sorted(set(direct) - set(local))
        sources[module] = {'path': path.relative_to(ROOT).as_posix(), 'sha256': sha(data),
            'bytes': len(data), 'local_imports': local, 'external_imports': boundary}
        pending.extend(local)
        for name in boundary:
            external[name].add(module)

    # Check acyclicity without assuming Python's recursion depth is sufficient.
    degree = {module: len(entry['local_imports']) for module, entry in sources.items()}
    importers = defaultdict(set)
    for module, entry in sources.items():
        for imported in entry['local_imports']:
            importers[imported].add(module)
    ready = [module for module, count in degree.items() if count == 0]
    heapq.heapify(ready)
    ordered = []
    while ready:
        module = heapq.heappop(ready)
        ordered.append(module)
        for importer in sorted(importers[module]):
            degree[importer] -= 1
            if degree[importer] == 0:
                heapq.heappush(ready, importer)
    require(len(ordered) == len(sources), 'Local source import graph has a cycle')
    sources = dict(sorted(sources.items()))
    for module, entry in sources.items():
        require(sha(source_path(module).read_bytes()) == entry['sha256'],
                'Source changed during inventory: ' + module)
    boundary_counts = {}
    for namespace in sorted({module.split('.')[0] for module in external}):
        names = [module for module in external if module.split('.')[0] == namespace]
        boundary_counts[namespace] = {'unique_modules': len(names),
            'local_to_external_import_edges': sum(len(external[module]) for module in names)}
    modules_text = ''.join(module + '\n' for module in sources)
    audit = audit_source(sources)
    digest_text = ''.join(module + '\t' + entry['path'] + '\t' + entry['sha256'] + '\n'
                          for module, entry in sources.items())
    inputs = [ROOT / 'lean-toolchain', ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json',
              Path(__file__).resolve(), HELPER_PATH, HERE / 'CheckEndpoint.lean']
    report = {'schema': 'hindman.final-target-source-preparation.v1',
        'status': 'prepared-source-inventory-only; Lean commands not executed', 'target': TARGET,
        'toolchain': toolchain, 'mathlib': mathlib[0]['rev'],
        'local_namespaces': sorted(NAMESPACES), 'local_source_modules': len(sources),
        'source_counts_by_namespace': dict(sorted(Counter(module.split('.')[0] for module in sources).items())),
        'local_import_edges': sum(len(entry['local_imports']) for entry in sources.values()),
        'acyclic': True, 'source_inventory_sha256': sha(digest_text.encode('utf-8')),
        'modules_list_sha256': sha(modules_text.encode('utf-8')),
        'all_declarations_audit_source_sha256': sha(audit.encode('utf-8')),
        'repository_input_sha256': {path.relative_to(ROOT).as_posix(): sha(path.read_bytes()) for path in inputs},
        'external_boundary_unique_modules': len(external),
        'external_boundary_import_edges': sum(len(importers) for importers in external.values()),
        'external_boundary_counts_by_namespace': boundary_counts,
        'external_sources_inventoried': False, 'compilation_executed': False,
        'axiom_audit_executed': False, 'kernel_replay_executed': False,
        'full_target_proved_by_this_preparation': False,
        'sources': sources,
        'external_boundary': {module: sorted(importers) for module, importers in sorted(external.items())}}
    return report, modules_text, audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', help='explicit repository directory for the prepared inventory/audit files')
    parser.add_argument('--replace-prepared', action='store_true', help='replace differing generated preparation files')
    args = parser.parse_args()
    require(not args.replace_prepared or args.output_dir, '--replace-prepared requires --output-dir')
    report, modules, audit = inventory()
    if args.output_dir:
        output = repo_path(args.output_dir)
        require(output.relative_to(ROOT).parts and output.relative_to(ROOT).parts[0]
                in {'verification', 'verification-local'}, 'Output must stay within verification or verification-local')
        files = {'source-closure.json': json.dumps(report, indent=2, ensure_ascii=True) + '\n',
                 'modules.txt': modules, 'CheckAllDeclarations.lean': audit}
        # Validate every existing destination before writing any of the outputs.
        for name, content in files.items():
            path = repo_path(output / name)
            require(not path.exists() or path.read_bytes() == content.encode('utf-8') or args.replace_prepared,
                    'Different existing preparation file preserved: ' + str(path))
        output.mkdir(parents=True, exist_ok=True)
        for name, content in files.items():
            path = repo_path(output / name)
            if not path.exists() or path.read_bytes() != content.encode('utf-8'):
                path.write_bytes(content.encode('utf-8'))
        report['generated_output_directory'] = output.relative_to(ROOT).as_posix()
    summary = {key: value for key, value in report.items() if key not in {'sources', 'external_boundary'}}
    print(json.dumps(summary, indent=2, ensure_ascii=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, UnicodeError) as error:
        print('Final-target preparation FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
