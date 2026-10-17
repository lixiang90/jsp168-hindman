#!/usr/bin/env python3
"""PREPARED ONLY: default preview; --archive writes only after real final gates.

No Lean, Lake, credential, network or publication command is run. The explicit
archive action calls the already-reviewed local publication gates and reruns the
Python audit-log parser. Original result/log bytes are never rewritten.
"""
import argparse
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path
import runpy
import subprocess
import sys
from types import SimpleNamespace
import zlib

ROOT = Path(__file__).resolve().parents[2]
PROOF_COMMIT = '7ae70219fb4034899c6c2d23cc3b58ec6730a1ba'
MANIFEST_SHA = '9176ef5a4f4d41b796269c88a90e23966ca62b17bef2a68060b12125886b9b7e'
SOURCE_INVENTORY_SHA = 'dcf81b5e67766bba2d3bb3f3cc1455e75940a47301e1f79efa9171f96d003796'
TARGET = 'Hindman168.JSP000168'
PREPARED = 'verification-local/final-target-7ae7021-2026-10-17'
BUILD = 'verification-local/build-jsp000168-resume12-2026-10-17'
SUITE = 'verification-local/final-suite-7ae7021-2026-10-17'
RAW_GIT = 'verification-local/git-byte-binding-7ae7021-2026-10-17'
PUBLIC_HELPER = 'verification-local/award-submission/publish-verified-repo.py'
PUBLIC_HELPER_SHA = '306677c510932b6b29459cb2c6a853d8c3706ec54b4a4c290892f5fd77e22866'
OUTPUT = ROOT / 'verification/original-final-target/verified-2026-10-17'


class ArchiveError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise ArchiveError(message)


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(131072), b''):
            h.update(block)
    return h.hexdigest()


def local_file(name):
    path = (ROOT / name).resolve()
    require(path.is_relative_to(ROOT) and path.is_file(), 'An allowlisted input is missing or outside the repository')
    return path


def load(name):
    return json.loads(local_file(name).read_bytes())


def mappings(summary):
    rows = []
    def add(source, destination, zipped=False):
        rows.append({'source': source, 'archive': destination, 'gzip': zipped})
    for name in ('source-closure.json', 'modules.txt', 'CheckAllDeclarations.lean'):
        add(PREPARED + '/' + name, 'prepared/' + name)
    for name in ('static-source-summary.json', 'static-source-detail.json'):
        add(PREPARED + '/' + name, 'static/' + name)
    for name in ('result.json', 'sources-before.json', 'sources-after.json'):
        add(BUILD + '/' + name, 'build/' + name)
    add(BUILD + '/build.log', 'build/build.log.gz', True)
    add(SUITE + '/result.json', 'suite/result.json')
    for name in ('01.log', '02.log', '03.log', 'artifacts-before.json', 'artifacts-after.json'):
        add(SUITE + '/' + name, 'suite/' + name + '.gz', True)
    add(summary, 'suite/audit-summary.json')
    for name in ('result.json', 'verify-git-blobs.py', 'preparation.json', 'source-change.diff',
                 'execution.json', 'execution.txt'):
        add(RAW_GIT + '/' + name, 'raw-git-binding/' + name)
    add(RAW_GIT + '/per-input-blobs.tsv', 'raw-git-binding/per-input-blobs.tsv.gz', True)
    # These nine files are exactly the prepared manifest's repository inputs.
    for source in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                   'verification/original-final-target/prepare.py',
                   'verification/original-upstream-inverse/verify-prepared.py',
                   'verification/original-final-target/CheckEndpoint.lean',
                   'verification/original-final-target/run-final-suite.py',
                   'verification/original-final-target/summarize-audit.py',
                   'verification/original-final-target/static-source-scan.py'):
        add(source, 'recorded-inputs/' + source)
    add('.gitattributes', 'recorded-inputs/.gitattributes')
    add('verification-local/run_build.py', 'recorded-tools/run_build.py')
    add(PUBLIC_HELPER, 'recorded-tools/publish-verified-repo.py')
    add(Path(__file__).resolve().relative_to(ROOT).as_posix(),
        'recorded-tools/archive-verified-evidence.py')
    require(len({r['source'] for r in rows}) == len(rows) and
            len({r['archive'] for r in rows}) == len(rows), 'Duplicate archive mapping')
    return rows


def gates(summary):
    manifest_path = PREPARED + '/source-closure.json'
    manifest = load(manifest_path)
    require(sha(local_file(manifest_path)) == MANIFEST_SHA and manifest['target'] == TARGET and
            manifest['source_inventory_sha256'] == SOURCE_INVENTORY_SHA and
            len(manifest['sources']) == 5066 and len(manifest['repository_input_sha256']) == 9,
            'The fixed final manifest differs')
    require(sha(local_file(PUBLIC_HELPER)) == PUBLIC_HELPER_SHA,
            'The reviewed local-gate implementation changed')
    helper = runpy.run_path(str(local_file(PUBLIC_HELPER)))
    repository_commit = helper['capture'](['git', 'rev-parse', 'HEAD'],
        'Archive repository HEAD check').strip()
    require(helper['SHA40'].fullmatch(repository_commit), 'Current repository HEAD is not a full commit SHA')
    helper['capture'](['git', 'merge-base', '--is-ancestor', PROOF_COMMIT, repository_commit],
        'Selected proof ancestry check')
    # Calling local_gates never invokes main(), credential retrieval or GitHub.
    # It checks clean current HEAD/main, P-manifest source/tool bytes, complete build and
    # all three suite exits, exact scope/log parser, environment and artifacts.
    helper['local_gates'](SimpleNamespace(commit=repository_commit, manifest=manifest_path,
        build_result=BUILD + '/result.json', suite_result=SUITE + '/result.json',
        audit_summary=summary))
    static = load(PREPARED + '/static-source-summary.json')
    require(static.get('manifest_file_sha256') == MANIFEST_SHA and
            static.get('manifest_source_inventory_sha256') == SOURCE_INVENTORY_SHA and
            static.get('scanner_sha256') == sha(local_file('verification/original-final-target/static-source-scan.py')) and
            static.get('primary_and_reduction_oracle_findings') == [] and
            static.get('summary', {}).get('manifest_source_hashes_match_at_scan') is True and
            static['summary'].get('all_scanned_sources_unchanged_at_end') is True,
            'The static report is not bound to this input checkpoint')
    detail = PREPARED + '/static-source-detail.json'
    require(static.get('detail_report', {}).get('path') == detail and
            static['detail_report'].get('sha256') == sha(local_file(detail)),
            'The static detail report differs')
    raw, execution, preparation = (load(RAW_GIT + '/' + name) for name in
                                   ('result.json', 'execution.json', 'preparation.json'))
    require(raw.get('selected_commit') == PROOF_COMMIT and raw.get('head_at_start') == PROOF_COMMIT and
            raw.get('head_at_end') == PROOF_COMMIT and raw.get('input_manifest_sha256') == MANIFEST_SHA and
            raw.get('source_inventory_sha256') == SOURCE_INVENTORY_SHA and
            helper['zero'](raw.get('actual_exit_code')) and helper['zero'](raw.get('git_cat_file_exit_code')) and
            helper['zero'](execution.get('actual_process_exit_code')) and
            raw.get('mismatches') == [] and raw.get('errors') == [], 'Raw Git byte binding did not pass')
    require(raw.get('counts') == {'attributes_checked': 1, 'attributes_identical': 1,
            'proof_checked': 5066, 'proof_identical': 5066,
            'repository-input_checked': 9, 'repository-input_identical': 9},
            'Raw Git byte-binding input coverage differs')
    raw_script = sha(local_file(RAW_GIT + '/verify-git-blobs.py'))
    require(raw.get('script_sha256') == raw_script == preparation.get('new_script_sha256') and
            raw.get('per_input_rows_sha256') == sha(local_file(RAW_GIT + '/per-input-blobs.tsv')) and
            execution.get('stdout_stderr_sha256') == sha(local_file(RAW_GIT + '/execution.txt')),
            'A raw Git binding script or log differs')
    parser = 'verification/original-final-target/summarize-audit.py'
    command = [sys.executable, parser, manifest_path, SUITE + '/02.log']
    started = datetime.now(timezone.utc).isoformat()
    process = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(process.returncode == 0, 'The fresh Python-only audit parser process did not pass')
    parsed = json.loads(process.stdout)
    require(parsed.get('passed') is True and parsed.get('manifest_sha256') == MANIFEST_SHA and
            parsed.get('source_inventory_sha256') == SOURCE_INVENTORY_SHA,
            'The fresh audit parser result is incomplete')
    parser_record = {'scope': 'Actual Python audit-log parser execution during archival gates; no Lean/Lake execution.',
        'command': command, 'started_utc': started,
        'finished_utc': datetime.now(timezone.utc).isoformat(), 'actual_exit_code': process.returncode,
        'stdout_sha256': hashlib.sha256(process.stdout).hexdigest(),
        'stderr_sha256': hashlib.sha256(process.stderr).hexdigest()}
    return manifest, process.stdout, process.stderr, parser_record, repository_commit


def copy_file(source, destination, zipped):
    before = source.stat()
    raw_hash = hashlib.sha256()
    raw_bytes = 0
    destination.parent.mkdir(parents=True, exist_ok=True)
    with source.open('rb') as stream, destination.open('xb') as file:
        target = gzip.GzipFile(filename='', mode='wb', fileobj=file, compresslevel=9, mtime=0) if zipped else file
        try:
            for block in iter(lambda: stream.read(131072), b''):
                raw_hash.update(block)
                raw_bytes += len(block)
                target.write(block)
        finally:
            if zipped:
                target.close()
    after = source.stat()
    require((before.st_size, before.st_mtime_ns) == (after.st_size, after.st_mtime_ns) and
            raw_bytes == before.st_size, 'An archive input changed while being copied')
    require(destination.stat().st_size < 100 * 1024 * 1024,
            'An archived file exceeds the 100-MiB publication bound')
    return {'source_bytes': raw_bytes, 'source_sha256': raw_hash.hexdigest(),
            'archive_bytes': destination.stat().st_size, 'archive_sha256': sha(destination),
            'encoding': 'gzip; empty filename; mtime=0; level=9' if zipped else 'raw bytes'}


def write_bytes(path, data):
    with path.open('xb') as stream:
        stream.write(data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit-summary', default=PREPARED + '/audit-summary.json',
                        help='Actual audit-summary.json in the fixed prepared or final suite directory')
    parser.add_argument('--archive', action='store_true', help='Explicitly perform gates and fresh archive creation')
    args = parser.parse_args()
    summary_path = (ROOT / args.audit_summary).resolve()
    allowed_summaries = {(ROOT / PREPARED / 'audit-summary.json').resolve(),
                         (ROOT / SUITE / 'audit-summary.json').resolve()}
    require(summary_path in allowed_summaries,
            'Audit summary must use one of the two fixed known audit-summary.json paths')
    summary = summary_path.relative_to(ROOT).as_posix()
    rows = mappings(summary)
    require(OUTPUT.resolve().is_relative_to(ROOT) and not OUTPUT.exists() and not OUTPUT.is_symlink(),
            'The fixed public output directory must be absent')
    if not args.archive:
        print(json.dumps({'status': 'preview only; gates and archive not executed',
            'proof_commit': PROOF_COMMIT, 'output': OUTPUT.relative_to(ROOT).as_posix(),
            'input_mapping': rows, 'lean_lake_network_credential_commands': False}, indent=2))
        return 0
    manifest, parser_stdout, parser_stderr, parser_record, repository_commit = gates(summary)
    for row in rows:
        local_file(row['source'])
    OUTPUT.mkdir(exist_ok=False)
    marker = OUTPUT / '_INCOMPLETE'
    write_bytes(marker, b'Archive not complete while this marker exists. Do not publish partial evidence.\n')
    index = {'schema': 'hindman.verified-evidence-byte-archive.v1',
        'proof_commit': PROOF_COMMIT, 'target': TARGET, 'source_manifest_sha256': MANIFEST_SHA,
        'current_repository_commit_at_archive': repository_commit,
        'source_inventory_sha256': SOURCE_INVENTORY_SHA,
        'archive_created_utc': datetime.now(timezone.utc).isoformat(),
        'archiver_sha256': sha(Path(__file__)), 'local_gates_source_sha256': PUBLIC_HELPER_SHA,
        'python_version': sys.version, 'zlib_version': zlib.ZLIB_VERSION,
        'zlib_runtime_version': zlib.ZLIB_RUNTIME_VERSION, 'files': []}
    for row in rows:
        source, destination = local_file(row['source']), OUTPUT / row['archive']
        require(destination.resolve().is_relative_to(OUTPUT.resolve()), 'An archive destination escapes')
        index['files'].append({**row, **copy_file(source, destination, row['gzip'])})
    # Rehash only the copied input files and the proof/tool sources. Do not run
    # another large artifact inventory here; the full local gate already did it.
    for entry in index['files']:
        require(sha(local_file(entry['source'])) == entry['source_sha256'],
                'A copied original changed before archival completion')
    expected = {entry['path']: entry['sha256'] for entry in manifest['sources'].values()}
    expected.update(manifest['repository_input_sha256'])
    require(all(sha(local_file(name)) == digest for name, digest in expected.items()),
            'A proof/tool input changed during archival copying')
    for name, data in [('parser-recheck.stdout.json', parser_stdout),
                       ('parser-recheck.stderr.log', parser_stderr),
                       ('parser-recheck-execution.json', (json.dumps(parser_record, indent=2) + '\n').encode())]:
        path = OUTPUT / name
        write_bytes(path, data)
        index.setdefault('generated_archival_parser_records', []).append(
            {'archive': name, 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()})
    readme = ("# Archived final verification evidence\n\n"
        "Original result JSON and source/log bytes are preserved. Their historical verification-local paths are not rewritten; archive-index.json maps each original source path to its public archived file. Decompress gzip files before comparing their source SHA256/bytes. Gzip uses an empty stored filename and mtime 0.\n\n"
        "The selected proof commit is " + PROOF_COMMIT + ". The all-declaration audit covers the actual local target closure; external unused declarations and external source rebuilding are outside that listing scope. Fresh replay uses Lean's own kernel for safe, nonpartial declarations. This is not an independent kernel or a claim of a cache-free rebuild. No award, first-proof, priority, authorship or payment determination is made.\n\n"
        "Recorded tool copies preserve executed bytes; reproduce with the original repository paths and pinned inputs, rather than executing the archival copies at changed directory depths. The separate parser-recheck files record an actual Python-only archival gate, not another Lean run. The archive is incomplete whenever _INCOMPLETE exists.\n").encode()
    write_bytes(OUTPUT / 'README.md', readme)
    index['generated_readme'] = {'archive': 'README.md', 'bytes': len(readme),
                                 'sha256': hashlib.sha256(readme).hexdigest()}
    index['finished_utc'] = datetime.now(timezone.utc).isoformat()
    write_bytes(OUTPUT / 'archive-index.json', (json.dumps(index, indent=2) + '\n').encode())
    marker.unlink()
    print(json.dumps({'status': 'archive completed; original evidence bytes preserved',
        'output': OUTPUT.relative_to(ROOT).as_posix(), 'proof_commit': PROOF_COMMIT,
        'archive_index_sha256': sha(OUTPUT / 'archive-index.json'),
        'copied_files': len(index['files']), 'publication_performed': False}, indent=2))
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except SystemExit:
        raise
    except BaseException:
        print(json.dumps({'status': 'archive not confirmed',
            'summary': 'A gate or copy check failed; preserve original evidence and any _INCOMPLETE directory for review. No credentials or input contents emitted.'}))
        raise SystemExit(1)
