#!/usr/bin/env python3
"""Read-only integrity checks for prepared OpenAI sources, without invoking Lean.

Default: check prepared-frontier-2026-10-17.json beside this script.
Repeat --manifest PATH to combine manifests. ``files`` may be a list of entries
or a mapping from module names to entries (the aggregate preparation format).
Paths in manifests and command-line paths are repository-relative; absolute
command-line paths are accepted only inside this repository.

Optional original files: --raw-root DIR, where DIR/OAI/.../Module.lean exists.
Without originals, modified-source blob/diff replay is explicitly unavailable.
Unmodified source bytes can themselves be checked against the original hashes.
No network authenticity, compilation, kernel replay or axiom audit is claimed.

Explicit generation only:
  --modules FILE --audit-output verification-local/PreparedAxioms.lean
Omit --modules to audit every module in the supplied manifests. The generated
non-module Lean file visits every target module's imported constNames, including
internal/private declarations, checks their transitive axioms and logs each name.
Run it separately with the pinned toolchain, for example:
  lake env lean -j1 --trust=0 -DautoImplicit=false verification-local/PreparedAxioms.lean
This axiom inspection is separate from leanchecker --fresh kernel replay.
"""

import argparse
import difflib
import hashlib
import json
from pathlib import Path, PurePosixPath, PureWindowsPath
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE_PREFIX = 'dependencies/openai-finite-szemeredi/'
DEFAULT_MANIFEST = HERE / 'prepared-frontier-2026-10-17.json'
MODULE_RE = re.compile(r'OAI(?:\.[A-Za-z_][A-Za-z_0-9]*)+\Z')
PINNED_COMMIT = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'
LOCAL_HEARTBEAT_DECLARATIONS = {
    'OAI.Combinatorics.Progressions.Estimates.UniformControlledCurrentStage':
        'exists_uniform_controlled_current_stage',
    'OAI.Combinatorics.Progressions.Geometry.NativeCoordinateDerivativeSystem':
        'exists_native_coordinate_derivative_system',
    'OAI.Combinatorics.Progressions.Polynomial.NativeFormalPolynomialSystems':
        'nativeFast_derivativeSystem_to_formal',
    'OAI.Combinatorics.Progressions.Estimates.ExtractedInitialState':
        'exists_fastCoefficient_rational_removal_grid',
    'OAI.Combinatorics.Progressions.Linear.FastKernelReabsorptionControl':
        'realFast_kernel_reabsorption_controlled',
    'OAI.Combinatorics.Progressions.Estimates.PositiveShiftRefilteredExpansion':
        'refiltered_product_expansion_of_recovered',
    'OAI.Combinatorics.Progressions.Estimates.UnnormalizedCommonSymbolFactorization':
        'common_coefficient_derivative_system',
    'OAI.Combinatorics.Progressions.Estimates.MarkedEvaluationJointBounds':
        'exists_markedShiftQuotient_bounded_direction_data',
    'OAI.Combinatorics.Progressions.Geometry.CommonMarkedDirectionCoordinates':
        'exists_native_marked_common_direction_coordinates',
}


def is_allowed_local_option(module, lines, index):
    """Allow only the recorded finite, declaration-local heartbeat ports."""
    command = 'set_option maxHeartbeats 1000000 in'
    declaration = LOCAL_HEARTBEAT_DECLARATIONS.get(module)
    if not declaration or lines[index].strip() != command:
        return False
    if sum(line.strip() == command for line in lines) != 1:
        return False
    following = next((line.strip() for line in lines[index + 1:] if line.strip()), '')
    return re.match(r'theorem\s+' + re.escape(declaration) + r'(?=\s|\(|:|$)', following) is not None


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def repo_path(value, *, manifest=False):
    require(isinstance(value, (str, Path)) and str(value), 'Empty or non-string path')
    value = str(value)
    if manifest:
        posix, windows = PurePosixPath(value), PureWindowsPath(value)
        require(not posix.is_absolute() and not windows.drive and '\\' not in value
                and '..' not in posix.parts and '\0' not in value,
                'Unsafe manifest path: ' + value)
    path = Path(value)
    if not path.is_absolute():
        path = ROOT / path
    path = path.resolve()
    require(path.is_relative_to(ROOT), 'Path escapes repository: ' + value)
    return path


def lean_code(text):
    """Remove nested comments and strings while preserving line boundaries."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                out.extend('  ')
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif string:
            if text[i] == '\\':
                out.extend('  ')
                i += 2
            elif text[i] == '"':
                string = False
                out.append(' ')
                i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.extend('  ')
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.extend(' ' * (end - i))
            i = end
        elif text[i] == '"':
            string = True
            out.append(' ')
            i += 1
        else:
            out.append(text[i])
            i += 1
    require(not depth and not string, 'Unterminated Lean comment/string')
    return ''.join(out)


def oai_imports(text):
    result = []
    for line in lean_code(text).splitlines():
        if re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+', line):
            result.extend(re.findall(r'\bOAI(?:\.[A-Za-z_0-9]+)+', line))
    return result


def module_path(module):
    require(isinstance(module, str) and MODULE_RE.fullmatch(module),
            'Invalid OAI module: ' + str(module))
    return repo_path(SOURCE_PREFIX + module.replace('.', '/') + '.lean', manifest=True)


def check(manifest_paths, raw_root=None):
    require((ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip()
            == 'leanprover/lean4:v4.32.2', 'Repository Lean toolchain changed')
    lockfile = json.loads((ROOT / 'lake-manifest.json').read_bytes())
    mathlib = [package for package in lockfile['packages'] if package['name'] == 'mathlib']
    require(len(mathlib) == 1 and mathlib[0]['rev']
            == '905b95818eb32af7874a58b427f50c1711a5e96c', 'Repository mathlib pin changed')
    entries, manifest_hashes = {}, {}
    for path in manifest_paths:
        data = path.read_bytes()
        manifest_hashes[path.relative_to(ROOT).as_posix()] = sha(data)
        manifest = json.loads(data)
        require(manifest.get('upstream_repository') == 'openai/math'
                and manifest.get('upstream_commit', manifest.get('fixed_upstream_commit')) == PINNED_COMMIT
                and manifest.get('fixed_upstream_commit', PINNED_COMMIT) == PINNED_COMMIT,
                'Wrong fixed upstream in ' + str(path))
        require(manifest.get('lean') == '4.32.2'
                and manifest.get('mathlib') == '905b95818eb32af7874a58b427f50c1711a5e96c',
                'Wrong toolchain/dependency pin in ' + str(path))
        files = manifest.get('files')
        require(isinstance(files, (list, dict)) and files,
                'Missing/empty files collection in ' + str(path))
        if isinstance(files, dict):
            require(all(key == entry['module'] for key, entry in files.items()),
                    'Aggregate module key mismatch: ' + str(path))
            files = list(files.values())
        require(len({entry['module'] for entry in files}) == len(files),
                'Duplicate module inside manifest: ' + str(path))
        if 'new_sources' in manifest:
            require(manifest['new_sources'] == len(files), 'Wrong aggregate source count')
        if 'exact_sources' in manifest:
            require(manifest['exact_sources'] == sum(entry['same_as_fixed_upstream'] for entry in files),
                    'Wrong aggregate exact-source count')
        if 'compatibility_ports' in manifest:
            require(manifest['compatibility_ports'] == sum(not entry['same_as_fixed_upstream'] for entry in files),
                    'Wrong aggregate compatibility-port count')
        for entry in files:
            module = entry['module']
            module_path(module)
            if module in entries:
                # Aggregate provenance and optional local originals may add metadata.
                core = lambda item: {key: value for key, value in item.items()
                                     if key not in {'raw_path', 'preparation_manifest'}}
                require(core(entries[module]) == core(entry), 'Conflicting duplicate module: ' + module)
                entry = {**entries[module], **entry}
            entries[module] = entry

    original_counts = {'raw_file_replayed': 0, 'identical_source_verified': 0,
                       'modified_original_unavailable': 0}
    unavailable, scans, allowed_options = [], [], []
    for module, entry in sorted(entries.items()):
        path = module_path(module)
        expected = SOURCE_PREFIX + module.replace('.', '/') + '.lean'
        require(entry['path'] == expected and repo_path(entry['path'], manifest=True) == path,
                'Wrong module source path: ' + module)
        upstream_path = 'lean/' + module.replace('.', '/') + '.lean'
        require(entry['upstream_path'] == upstream_path, 'Wrong upstream path: ' + module)
        for key, length in [('ported_sha256', 64), ('upstream_sha256', 64), ('upstream_blob', 40)]:
            require(isinstance(entry.get(key), str)
                    and re.fullmatch('[0-9a-f]{' + str(length) + '}', entry[key]),
                    'Invalid ' + key + ': ' + module)
        current = path.read_bytes()
        require(sha(current) == entry['ported_sha256'], 'Prepared SHA256 mismatch: ' + module)
        require(len(current) == entry['ported_bytes'], 'Prepared byte count mismatch: ' + module)
        imports = oai_imports(current.decode('utf-8'))
        require(imports == entry['oai_imports'], 'Manifest import list mismatch: ' + module)
        for imported in imports:
            require(module_path(imported).is_file(), 'Missing OAI import: ' + imported)
        diff = entry['full_diff']
        require(isinstance(diff, str), 'Non-string full_diff: ' + module)
        identical = entry['upstream_sha256'] == entry['ported_sha256']
        require(entry['same_as_fixed_upstream'] is identical,
                'Inconsistent same_as_fixed_upstream: ' + module)
        require((diff == '') is identical, 'Diff/hash consistency mismatch: ' + module)
        if diff:
            require(diff.startswith('--- ' + upstream_path + '\n+++ ' + expected + '\n@@ '),
                    'Unexpected full_diff headers: ' + module)
        if 'upstream_blob_recomputed' in entry:
            require(entry['upstream_blob_recomputed'] == entry['upstream_blob'],
                    'Inconsistent recorded original blob: ' + module)
        raw_path = repo_path(entry['raw_path'], manifest=True) if entry.get('raw_path') else None
        if raw_root is not None:
            candidate = (raw_root / (module.replace('.', '/') + '.lean')).resolve()
            require(candidate.is_relative_to(raw_root) and candidate.is_relative_to(ROOT),
                    'Original path escapes raw root: ' + module)
            if candidate.is_file():
                raw_path = candidate
        if raw_path is not None and raw_path.is_file():
            original = raw_path.read_bytes()
            require(sha(original) == entry['upstream_sha256'], 'Original SHA256 mismatch: ' + module)
            require(blob(original) == entry['upstream_blob'], 'Original Git blob mismatch: ' + module)
            require(len(original) == entry['raw_bytes'], 'Original byte count mismatch: ' + module)
            actual = ''.join(difflib.unified_diff(original.decode('utf-8').splitlines(keepends=True),
                current.decode('utf-8').splitlines(keepends=True),
                fromfile=upstream_path, tofile=expected))
            require(actual == diff, 'Original-to-prepared full_diff mismatch: ' + module)
            original_counts['raw_file_replayed'] += 1
        elif identical:
            require(blob(current) == entry['upstream_blob'], 'Identical original blob mismatch: ' + module)
            require(len(current) == entry['raw_bytes'], 'Identical original byte count mismatch: ' + module)
            original_counts['identical_source_verified'] += 1
        else:
            original_counts['modified_original_unavailable'] += 1
            unavailable.append(module)
        code_lines = lean_code(current.decode('utf-8')).splitlines()
        for number, line in enumerate(code_lines, 1):
            if re.search(r'\b(?:sorry|admit|axiom|unsafe|extern|native_decide|implemented_by)\b', line):
                scans.append({'module': module, 'line': number, 'code': line.strip()})
            if re.search(r'\bset_option\b', line):
                # A finite budget is permitted only at its recorded declaration.
                allowed = is_allowed_local_option(module, code_lines, number - 1)
                finding = {'module': module, 'line': number, 'code': line.strip()}
                (allowed_options if allowed else scans).append(finding)
    require(not scans, 'Strict-source scan found disallowed constructs: ' + json.dumps(scans))
    seen, pending = set(), list(entries)
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        path = module_path(module)
        require(path.is_file(), 'Missing transitive OAI source: ' + module)
        pending.extend(oai_imports(path.read_bytes().decode('utf-8')))
    status = ('prepared-sources-passed-with-unreplayed-originals' if unavailable
              else 'prepared-source-integrity-passed')
    return entries, {'status': status,
        'manifest_sha256': manifest_hashes, 'prepared_modules': len(entries),
        'transitive_oai_sources_present': len(seen), 'original_checks': original_counts,
        'original_blob_and_diff_not_replayed': unavailable,
        'strict_source_scan_findings': scans, 'allowed_elaboration_options': allowed_options,
        'limitations': 'Local consistency only; no remote authentication, Lean build, kernel replay or axiom audit executed.'}


def audit_source(modules):
    """All declarations in each target module, never a selected theorem sample."""
    modules = sorted(set(modules))
    for module in modules:
        module_path(module)
    return ('/- Generated by verify-prepared.py. No Lean execution is implied. -/\n'
        + '\n'.join('import ' + module for module in modules)
        + '\nimport Lean\n\nopen Lean Elab Command\n'
        + 'set_option maxRecDepth 10000\nset_option maxHeartbeats 0\n\nrun_cmd do\n'
        + '  let env ← getEnv\n  let targets : List Name := ['
        + ', '.join('`' + module for module in modules) + ']\n'
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
        + '  logInfo m!"AUDIT COMPLETE: {found.size} modules; {seen.size} unique declarations; {records} records; only standard three axioms"\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--manifest', action='append', help='prepared files-list manifest; repeat to combine')
    parser.add_argument('--raw-root', help='optional original source directory containing OAI/')
    parser.add_argument('--modules', help='newline-separated OAI audit target list')
    parser.add_argument('--audit-output', help='explicit path at which to generate the Lean audit source')
    args = parser.parse_args()
    require(not args.modules or args.audit_output, '--modules requires --audit-output')
    paths = [repo_path(path) for path in args.manifest] if args.manifest else [DEFAULT_MANIFEST]
    raw_root = repo_path(args.raw_root) if args.raw_root else None
    entries, summary = check(paths, raw_root)
    if args.audit_output:
        modules = sorted(entries)
        if args.modules:
            modules = repo_path(args.modules).read_text(encoding='utf-8-sig').splitlines()
            require(modules and all(line.strip() == line and MODULE_RE.fullmatch(line) for line in modules),
                    'Invalid or empty module list')
            require(len(set(modules)) == len(modules), 'Duplicate audit modules')
        require(all(module_path(module).is_file() for module in modules), 'Missing audit target source')
        output = repo_path(args.audit_output)
        require(output.suffix == '.lean' and output != Path(__file__).resolve()
                and output.relative_to(ROOT).parts[0] not in {'.git', '.agents', '.codex', '.aws'}
                and not output.is_relative_to(ROOT / 'dependencies')
                and not output.is_relative_to(ROOT / 'Hindman168'), 'Unsafe audit output location')
        generated = audit_source(modules).encode('utf-8')
        if output.exists():
            require(output.read_bytes() == generated, 'Refusing to overwrite a different existing audit source')
        else:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(generated)
        summary['generated_audit'] = {'path': output.relative_to(ROOT).as_posix(), 'sha256': sha(generated),
            'target_modules': len(modules), 'target_modules_not_hash_checked_by_these_manifests':
            sorted(set(modules) - entries.keys()), 'executed': False}
    print(json.dumps(summary, indent=2, ensure_ascii=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, UnicodeError) as error:
        print('Prepared-source check FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
