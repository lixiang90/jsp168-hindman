"""Read-only binary Git-blob/worktree/manifest comparison; no Lean/Lake/network."""
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath, PureWindowsPath
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
COMMIT = '7ae70219fb4034899c6c2d23cc3b58ec6730a1ba'
MANIFEST = ROOT / 'verification-local/final-target-7ae7021-2026-10-17/source-closure.json'
REPORT = HERE / 'result.json'
ROWS = HERE / 'per-input-blobs.tsv'
ENV = {**os.environ, 'GIT_OPTIONAL_LOCKS': '0', 'GIT_TERMINAL_PROMPT': '0'}


def git(arguments, *, input_bytes=None, allow_unset=False):
    result = subprocess.run(['git', *arguments], cwd=ROOT, env=ENV,
                            input=input_bytes, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode and not (allow_unset and result.returncode == 1):
        raise RuntimeError('Read-only Git command failed')
    return result.returncode, result.stdout


def sha_file(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(131072), b''):
            digest.update(chunk)
    return digest.hexdigest()


def source_path(name):
    pure = PurePosixPath(name)
    if (not isinstance(name, str) or pure.is_absolute() or PureWindowsPath(name).drive or
        '..' in pure.parts or '\\' in name or any(c in name for c in '\0\n\r\t')):
        raise RuntimeError('Unsafe manifest source path')
    path = (ROOT / name).resolve()
    if not path.is_relative_to(ROOT):
        raise RuntimeError('Manifest source escapes repository')
    return path


def config_value(name):
    code, value = git(['config', '--get', name], allow_unset=True)
    return {'set': code == 0, 'value': value.decode('utf-8').strip() if code == 0 else None}


if REPORT.exists() or ROWS.exists():
    raise SystemExit('Checkpoint output already exists; preserve it and choose a new directory')
manifest_bytes = MANIFEST.read_bytes()
manifest = json.loads(manifest_bytes)
entries = {}
for module, entry in manifest['sources'].items():
    entries[entry['path']] = {'category': 'proof', 'module': module, 'sha256': entry['sha256']}
for name, digest in manifest['repository_input_sha256'].items():
    if name in entries:
        raise RuntimeError('Duplicate proof/tool path')
    entries[name] = {'category': 'repository-input', 'sha256': digest}

report = {
    'schema': 'hindman.selected-commit-raw-git-byte-binding.v1',
    'scope': 'Raw selected-commit Git blobs versus current worktree and manifest; NOT Lean verification evidence.',
    'selected_commit': COMMIT, 'started_utc': datetime.now(timezone.utc).isoformat(),
    'input_manifest': MANIFEST.relative_to(ROOT).as_posix(),
    'input_manifest_sha256': hashlib.sha256(manifest_bytes).hexdigest(),
    'source_inventory_sha256': manifest['source_inventory_sha256'],
    'script_sha256': sha_file(Path(__file__)),
    'expected_proof_sources': len(manifest['sources']),
    'expected_repository_inputs': len(manifest['repository_input_sha256']),
    'counts': {}, 'mismatches': [], 'errors': [], 'actual_exit_code': None,
    'method': 'One git cat-file --batch process, binary pipes, one request/response at a time; stream SHA256 and canonical Git SHA1 without text/EOL conversion or per-file spawning.',
    'lean_executed': False, 'lake_executed': False, 'network_used': False,
}
batch = None
try:
    report['head_at_start'] = git(['rev-parse', 'HEAD'])[1].decode().strip()
    if report['head_at_start'] != COMMIT:
        raise RuntimeError('HEAD differs from selected checkpoint')
    report['git_config'] = {name: config_value(name) for name in
                            ('core.autocrlf', 'core.eol', 'core.attributesfile')}
    attr_paths = git(['ls-files', '-z', '--', '.gitattributes', '**/.gitattributes'])[1].decode().split('\0')
    attr_paths = [name for name in attr_paths if name]
    report['tracked_attribute_paths'] = attr_paths
    report['git_info_attributes_exists'] = (ROOT / '.git/info/attributes').is_file()
    attr_input = b''.join(name.encode('utf-8') + b'\0' for name in sorted(entries))
    attr_raw = git(['check-attr', '-z', '--stdin', 'text', 'eol', 'working-tree-encoding'], input_bytes=attr_input)[1]
    attr_fields = attr_raw.decode('utf-8').split('\0')
    if attr_fields[-1] == '':
        attr_fields.pop()
    if len(attr_fields) != 3 * 3 * len(entries):
        raise RuntimeError('Unexpected effective attribute record count')
    attrs = Counter()
    attr_exceptions = []
    for index in range(0, len(attr_fields), 3):
        name, attribute, value = attr_fields[index:index+3]
        attrs[attribute + '=' + value] += 1
        if attribute == 'text' and value != 'unset':
            attr_exceptions.append({'path': name, 'attribute': attribute, 'value': value})
    report['effective_attribute_counts'] = dict(sorted(attrs.items()))
    report['effective_text_attribute_exceptions'] = attr_exceptions
    batch = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=ROOT, env=ENV,
                             stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    counts = Counter()
    objects = set()
    scanned_hashes = {}

    def compare(name, category, expected=None):
        batch.stdin.write((COMMIT + ':' + name + '\n').encode('utf-8'))
        batch.stdin.flush()
        header = batch.stdout.readline()
        if header.endswith(b' missing\n'):
            item = {'path': name, 'category': category, 'git_blob_missing': True}
            report['mismatches'].append(item)
            print('MISMATCH: missing Git blob: ' + name, flush=True)
            return
        fields = header.rstrip(b'\n').split(b' ')
        if len(fields) != 3:
            raise RuntimeError('Invalid binary cat-file header')
        oid, kind, length = fields[0].decode(), fields[1].decode(), int(fields[2])
        digest = hashlib.sha256()
        blob_digest = hashlib.sha1(b'blob ' + str(length).encode() + b'\0')
        remaining = length
        while remaining:
            chunk = batch.stdout.read(min(remaining, 131072))
            if not chunk:
                raise RuntimeError('Truncated binary cat-file response')
            digest.update(chunk)
            blob_digest.update(chunk)
            remaining -= len(chunk)
        if batch.stdout.read(1) != b'\n':
            raise RuntimeError('Invalid binary cat-file record terminator')
        path = source_path(name)
        worktree = sha_file(path) if path.is_file() else None
        scanned_hashes[name] = worktree
        git_sha = digest.hexdigest()
        counts[category + '_checked'] += 1
        objects.add(oid)
        row = [category, name, oid, str(length), git_sha, worktree or 'MISSING', expected or 'NOT-IN-MANIFEST']
        rows.write('\t'.join(row) + '\n')
        okay = kind == 'blob' and blob_digest.hexdigest() == oid and git_sha == worktree and (expected is None or git_sha == expected)
        if okay:
            counts[category + '_identical'] += 1
        else:
            report['mismatches'].append({'path': name, 'category': category, 'git_blob': oid,
                                         'git_kind': kind, 'git_blob_sha256': git_sha,
                                         'worktree_sha256': worktree, 'manifest_sha256': expected,
                                         'canonical_git_blob_id_matches': blob_digest.hexdigest() == oid})
            print('MISMATCH: raw Git/worktree/manifest bytes differ: ' + name, flush=True)

    with ROWS.open('w', encoding='utf-8', newline='\n') as rows:
        rows.write('category\tpath\tgit_blob_sha1\tgit_blob_bytes\tgit_blob_sha256\tworktree_sha256\tmanifest_sha256\n')
        for name, entry in sorted(entries.items()):
            compare(name, entry['category'], entry['sha256'])
        for name in attr_paths:
            compare(name, 'attributes')
    batch.stdin.close()
    batch.wait()
    report['git_cat_file_exit_code'] = batch.returncode
    if batch.returncode:
        raise RuntimeError('Binary git cat-file process failed')
    for name, scanned in scanned_hashes.items():
        path = source_path(name)
        current = sha_file(path) if path.is_file() else None
        if current != scanned:
            report['mismatches'].append({'path': name, 'changed_during_read': True})
            print('MISMATCH: source changed during read: ' + name, flush=True)
    report['head_at_end'] = git(['rev-parse', 'HEAD'])[1].decode().strip()
    if report['head_at_end'] != COMMIT:
        report['errors'].append('HEAD changed during the selected-commit read')
    if MANIFEST.read_bytes() != manifest_bytes:
        report['errors'].append('Input manifest changed during the read')
    report['counts'] = dict(sorted(counts.items()))
    report['unique_git_blob_objects'] = len(objects)
    report['per_input_rows'] = ROWS.relative_to(ROOT).as_posix()
    report['per_input_rows_sha256'] = sha_file(ROWS)
    report['attributes_contents'] = {name: source_path(name).read_text(encoding='utf-8') for name in attr_paths}
    report['attribute_explanation'] = 'core.autocrlf=input is a global normalization default. The repository * -text rule disables text/EOL conversion for these paths; effective text=unset is checked per input. Raw byte equality above is the direct evidence and does not rely on git diff cleanliness.'
except Exception as error:
    report['errors'].append(type(error).__name__ + ': ' + str(error))
finally:
    if batch is not None and batch.poll() is None:
        batch.kill()
        batch.wait()
    report['finished_utc'] = datetime.now(timezone.utc).isoformat()
    report['actual_exit_code'] = 0 if not report['mismatches'] and not report['errors'] else 1
    report['status'] = 'raw bytes identical' if report['actual_exit_code'] == 0 else 'mismatch or incomplete verification'
    REPORT.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(report, indent=2))
raise SystemExit(report['actual_exit_code'])
