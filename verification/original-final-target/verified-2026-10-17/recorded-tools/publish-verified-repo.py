#!/usr/bin/env python3
"""PREPARED, NOT EXECUTED: publish only lixiang90/jsp168-hindman after verification.

Required: --commit 40_SHA --manifest FILE --build-result FILE --suite-result FILE
          --audit-summary FILE
Execution changes visibility only after all local gates and authenticated
read-only repository/main checks. This file has not been run for publication.
The credential is obtained noninteractively only after local verification,
kept in process memory, and passed to child gh through GH_TOKEN. Never log it.
No proof build, Lean execution, push, PR, or message is performed by this helper.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath, PureWindowsPath
import re
import runpy
import subprocess

ROOT = Path(__file__).resolve().parents[2]
REPO = 'lixiang90/jsp168-hindman'
TARGET = 'Hindman168.JSP000168'
TOOLCHAIN = 'leanprover/lean4:v4.32.2'
SHA40 = re.compile(r'[0-9a-f]{40}\Z')
SHA256 = re.compile(r'[0-9a-f]{64}\Z')
WRITE_ATTEMPTED = False


class GateError(Exception):
    """Only fixed, secret-free messages may be raised here."""


def require(condition, message):
    if not condition:
        raise GateError(message)


def zero(value):
    return type(value) is int and value == 0


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def confined(value):
    path = Path(value)
    if not path.is_absolute():
        path = ROOT / path
    path = path.resolve()
    require(path.is_relative_to(ROOT), 'An evidence path escapes the repository')
    return path


def relative_file(value):
    require(isinstance(value, str) and value and '\\' not in value, 'Invalid relative evidence path')
    parts = PurePosixPath(value)
    require(not parts.is_absolute() and not PureWindowsPath(value).drive and
            '..' not in parts.parts and '\0' not in value, 'Invalid relative evidence path')
    return confined(value)


def load(path, label):
    try:
        return json.loads(path.read_bytes())
    except Exception:
        raise GateError('Could not read ' + label) from None


def timestamp(value):
    try:
        stamp = datetime.fromisoformat(value.replace('Z', '+00:00'))
        require(stamp.tzinfo is not None, 'A verification timestamp has no timezone')
        return stamp
    except GateError:
        raise
    except Exception:
        raise GateError('Invalid verification timestamp') from None


def clean_environment():
    env = dict(os.environ)
    for name in list(env):
        if name.startswith(('GH_DEBUG', 'GIT_TRACE', 'GCM_TRACE')) or name in {
            'GIT_CURL_VERBOSE', 'GH_TOKEN', 'GITHUB_TOKEN', 'GH_ENTERPRISE_TOKEN', 'GITHUB_ENTERPRISE_TOKEN'}:
            env.pop(name, None)
    env.update(GIT_TERMINAL_PROMPT='0', GCM_INTERACTIVE='never', GCM_GUI_PROMPT='0',
               GH_PROMPT_DISABLED='1', GH_HOST='github.com')
    return env


def capture(arguments, label, *, env=None, text_input=None, timeout=120):
    try:
        result = subprocess.run(arguments, cwd=ROOT, env=env or clean_environment(),
                                input=text_input, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                text=True, encoding='utf-8', errors='replace', timeout=timeout)
    except Exception:
        raise GateError(label + ' could not run') from None
    require(result.returncode == 0, label + ' failed')
    return result.stdout


def identity(commit):
    require(capture(['git', 'rev-parse', 'HEAD'], 'Local HEAD check').strip() == commit,
            'Local HEAD differs from the selected commit')
    require(capture(['git', 'rev-parse', 'refs/heads/main'], 'Local main check').strip() == commit,
            'Local main differs from the selected commit')
    require(not capture(['git', 'status', '--porcelain', '--untracked-files=normal'], 'Worktree check').strip(),
            'The repository worktree is not clean')
    origin = capture(['git', 'remote', 'get-url', 'origin'], 'Origin check').strip()
    require(origin in {f'https://github.com/{REPO}', f'https://github.com/{REPO}.git',
                       f'git@github.com:{REPO}', f'git@github.com:{REPO}.git'},
            'Origin differs from the fixed repository')


def expected_commands(manifest_path):
    audit = (manifest_path.parent / 'CheckAllDeclarations.lean').relative_to(ROOT).as_posix()
    return [
        ['lake', 'env', 'lean', '-j1', '--trust=0', '-DautoImplicit=false',
         'verification/original-final-target/CheckEndpoint.lean'],
        ['lake', 'env', 'lean', '-j1', '--trust=0', '-DautoImplicit=false', audit],
        ['lake', 'env', 'leanchecker', '--fresh', '--verbose', TARGET],
    ]


def validate_suite_commands(suite, commands):
    records = suite.get('commands', [])
    require(len(records) == 3, 'The final suite did not record exactly three checks')
    for record, expected in zip(records, commands):
        require(record.get('command') == expected and record.get('status') == 'passed' and
                zero(record.get('exit_code')), 'A final verification command is missing or did not pass')
    require([record.get('log') for record in records] == ['01.log', '02.log', '03.log'],
            'The suite log selection is incomplete')


def validate_build_binding(build, build_path, manifest):
    require(zero(build.get('wrapper_exit_code')) and build.get('source_inputs_unchanged') is True,
            'The whole build has no successful unchanged-source binding')
    require(build.get('runner_sha256') == sha(ROOT / 'verification-local/run_build.py'),
            'The whole-build recording tool differs')
    snapshots = []
    for name, key in [('sources-before.json', 'sources_before_sha256'),
                      ('sources-after.json', 'sources_after_sha256')]:
        path = build_path.parent / name
        require(path.is_file() and sha(path) == build.get(key), 'A whole-build source snapshot differs')
        snapshots.append(load(path, 'whole-build source snapshot'))
    require(snapshots[0] == snapshots[1] == manifest,
            'The whole build did not use the complete selected source and tool inputs')
    log_path = build_path.parent / 'build.log'
    require(log_path.is_file() and sha(log_path) == build.get('build_log_sha256'),
            'The whole-build result is not bound to its actual stdout log')


def local_gates(args):
    manifest_path, build_path, suite_path, summary_path = (
        confined(value) for value in (args.manifest, args.build_result, args.suite_result, args.audit_summary))
    manifest, build, suite, summary = (load(path, label) for path, label in (
        (manifest_path, 'selected manifest'), (build_path, 'whole build result'),
        (suite_path, 'final suite result'), (summary_path, 'full audit summary')))
    require(build.get('status') == 'passed' and zero(build.get('exit_code')) and
            build.get('command') in (['lake', '-v', 'build', TARGET], ['lake', 'build', TARGET]),
            'The complete final-target build did not pass')
    require(suite.get('status') == 'passed' and zero(suite.get('whole_suite_exit_code')) and
            suite.get('target') == TARGET, 'The complete final suite did not pass')
    require(summary.get('passed') is True and not summary.get('errors'), 'The full audit summary did not pass')
    validate_build_binding(build, build_path, manifest)
    identity(args.commit)
    require(manifest.get('target') == TARGET and manifest.get('toolchain') == TOOLCHAIN,
            'Wrong manifest target or toolchain')
    manifest_sha = sha(manifest_path)
    require(suite.get('manifest_sha256') == manifest_sha and summary.get('manifest_sha256') == manifest_sha and
            suite.get('manifest') == manifest_path.relative_to(ROOT).as_posix(),
            'Manifest hashes or selected paths do not agree')
    require(summary.get('source_inventory_sha256') == manifest.get('source_inventory_sha256'),
            'Audit source-inventory hash does not agree')
    sources, inputs = manifest.get('sources', {}), manifest.get('repository_input_sha256', {})
    require(sources and len(sources) == manifest.get('local_source_modules') and inputs,
            'Incomplete source/tool inventory')
    expected = {entry['path']: entry['sha256'] for entry in sources.values()}
    expected.update(inputs)
    audit_path = manifest_path.parent / 'CheckAllDeclarations.lean'
    expected[audit_path.relative_to(ROOT).as_posix()] = manifest['all_declarations_audit_source_sha256']
    for name, digest in expected.items():
        path = relative_file(name)
        require(SHA256.fullmatch(digest) and path.is_file() and sha(path) == digest,
                'A selected source, tool, or generated audit differs')
    require(sha(manifest_path.parent / 'modules.txt') == manifest['modules_list_sha256'],
            'The generated module list differs')
    tracked = set(capture(['git', 'ls-files', '-z'], 'Tracked input check').split('\0'))
    require(all(name in tracked for name in [*(entry['path'] for entry in sources.values()), *inputs]),
            'A proof or verification-tool input is not tracked')
    # Regenerate the actual complete current closure; do not accept a partial passed manifest.
    current = runpy.run_path(str(ROOT / 'verification/original-final-target/prepare.py'))['inventory']()[0]
    for key in ('target', 'toolchain', 'mathlib', 'sources', 'repository_input_sha256',
                'source_inventory_sha256', 'modules_list_sha256', 'all_declarations_audit_source_sha256',
                'local_source_modules', 'external_boundary'):
        require(current.get(key) == manifest.get(key), 'The selected manifest differs from the current complete target inventory')
    validate_suite_commands(suite, expected_commands(manifest_path))
    for stage in ('sources_before', 'sources_after'):
        check = suite.get(stage, {})
        require(check.get('passed') is True and not check.get('mismatches') and check.get('files') == len(expected),
                'The suite source-input checks are incomplete')
    environment = suite.get('environment_after', {})
    require(environment.get('passed') is True and environment == suite.get('environment_before') and
            not suite.get('changed_artifacts'), 'The suite environment/artifact checks are incomplete')
    build_finished = timestamp(build.get('finished_utc'))
    suite_started, suite_finished = timestamp(suite.get('started_utc')), timestamp(suite.get('finished_utc'))
    require(timestamp(build.get('started_utc')) <= build_finished <= suite_started <= suite_finished <= datetime.now(timezone.utc),
            'Build and suite timestamps are inconsistent')
    require(build_finished <= timestamp(build.get('binding_finished_utc')) <= suite_started,
            'The whole-build source binding did not finish before the final suite')
    previous_finished = suite_started
    for record in suite['commands']:
        started, finished = timestamp(record.get('started_utc')), timestamp(record.get('finished_utc'))
        require(previous_finished <= started <= finished <= suite_finished,
                'Verification command timestamps are inconsistent')
        previous_finished = finished
        require((suite_path.parent / record['log']).is_file(), 'A final suite stdout log is missing')
    require(b'replaying Hindman168.JSP000168 with --fresh' in (suite_path.parent / '03.log').read_bytes(),
            'The verbose fresh-kernel replay log is missing')
    require(all(relative_file(entry['path']).stat().st_mtime <= build_finished.timestamp() + 1
                for entry in sources.values()), 'A current proof source is newer than the successful whole build')
    build_log = build_path.parent / 'build.log'
    require(build_log.is_file() and b'Build completed successfully' in build_log.read_bytes(),
            'The successful whole build log is missing')
    # Bind the parsed summary to the actual audit stdout and reparse all records.
    log_path = suite_path.parent / suite['commands'][1]['log']
    require(log_path.resolve().is_relative_to(suite_path.parent) and sha(log_path) == summary.get('log_sha256') and
            log_path.stat().st_size == summary.get('log_bytes'), 'The audit summary is not bound to the suite log')
    parser_path = ROOT / 'verification/original-final-target/summarize-audit.py'
    require(summary.get('parser_sha256') == sha(parser_path), 'The audit parser hash differs')
    parser = runpy.run_path(str(parser_path))['parse_audit']
    with log_path.open(encoding='utf-8') as stream:
        parsed = parser(manifest, stream)
    require(parsed.get('passed') is True and all(summary.get(key) == value for key, value in parsed.items()),
            'Full audit records, module scope, counts, or axioms do not agree')
    # Recheck the exact artifacts and environment that the successful suite used.
    installed = Path(os.environ.get('ELAN_HOME', str(Path.home() / '.elan'))) / 'toolchains' / TOOLCHAIN.replace('/', '--').replace(':', '---')
    before_path, after_path = suite_path.parent / 'artifacts-before.json', suite_path.parent / 'artifacts-after.json'
    require(sha(before_path) == suite.get('artifacts_before_sha256') and sha(after_path) == suite.get('artifacts_after_sha256'),
            'The suite artifact inventory hashes differ')
    before, after = load(before_path, 'before artifact inventory'), load(after_path, 'after artifact inventory')
    require(before == after and after and len(after) == suite.get('artifact_files'), 'The suite artifact inventories differ')
    require(all('.lake/build/lib/lean/' + module.replace('.', '/') + '.olean' in after for module in sources),
            'The suite artifact inventory omits a local proof module')
    for name, entry in after.items():
        if name.startswith('<pinned-toolchain>/lib/lean/'):
            tail = name[len('<pinned-toolchain>/lib/lean/'):]
            path = (installed / 'lib/lean' / tail).resolve()
            require(path.is_relative_to((installed / 'lib/lean').resolve()), 'Invalid toolchain artifact path')
        else:
            require(name.startswith('.lake/'), 'Invalid repository artifact path')
            path = relative_file(name)
        require(path.is_file() and path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256'],
                'A verified proof artifact has changed')
    binaries = environment.get('toolchain_binary_sha256', {})
    require({'lean.exe', 'lake.exe', 'leanchecker.exe'} <= set(binaries), 'The Windows toolchain binary record is incomplete')
    for name, digest in binaries.items():
        require(Path(name).name == name and sha(installed / 'bin' / name) == digest,
                'A verified toolchain binary has changed')
    package_records = environment.get('packages', [])
    pinned_packages = {p['name']: p['rev'] for p in load(ROOT / 'lake-manifest.json', 'dependency pins')['packages']}
    require(len(package_records) == len(pinned_packages) and
            {p['name']: p['pinned'] for p in package_records} == pinned_packages,
            'The verified dependency environment is incomplete')
    require('version 4.32.2,' in environment.get('lean_version', ''), 'The recorded Lean version differs')
    for package in package_records:
        path = relative_file('.lake/packages/' + package['name'])
        require(package.get('head') == package.get('pinned') and not package.get('tracked_status') and
                capture(['git', '-C', str(path), 'rev-parse', 'HEAD'], 'Dependency HEAD check').strip() == package['pinned'] and
                not capture(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], 'Dependency status check').strip(),
                'A verified dependency has changed')
    identity(args.commit)


def validate_remote(repo, branch, commit):
    require(repo.get('full_name') == REPO and repo.get('owner', {}).get('login') == 'lixiang90' and
            repo.get('permissions', {}).get('admin') is True and repo.get('default_branch') == 'main' and
            type(repo.get('private')) is bool, 'Authenticated repository identity or admin permission check failed')
    require(branch.get('object', {}).get('type') == 'commit' and branch.get('object', {}).get('sha') == commit,
            'Authenticated remote main differs from the selected commit')


def main():
    global WRITE_ATTEMPTED
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('commit', 'manifest', 'build-result', 'suite-result', 'audit-summary'):
        parser.add_argument('--' + name, required=True)
    args = parser.parse_args()
    args.commit = args.commit.lower()
    require(SHA40.fullmatch(args.commit), 'A full 40-character commit SHA is required')
    local_gates(args)
    token, gh_env = None, None
    try:
        # First credential access: after all local proof/evidence/clean gates.
        raw = capture(['git', 'credential', 'fill'], 'Credential retrieval',
                      text_input=f'protocol=https\nhost=github.com\npath={REPO}.git\nusername=lixiang90\n\n')
        credential = dict(line.split('=', 1) for line in raw.splitlines() if '=' in line)
        token = credential.get('password')
        require(isinstance(token, str) and token and '\0' not in token, 'No usable repository credential is available')
        raw, credential = '', {}
        gh_env = clean_environment()
        gh_env['GH_TOKEN'] = token
        def get(endpoint):
            body = capture(['gh', 'api', '--hostname', 'github.com', '--method', 'GET', endpoint],
                           'Authenticated read-only GitHub check', env=gh_env)
            try:
                return json.loads(body)
            except Exception:
                raise GateError('Authenticated GitHub response was invalid') from None
        repo, branch = get('repos/' + REPO), get('repos/' + REPO + '/git/ref/heads/main')
        validate_remote(repo, branch, args.commit)
        identity(args.commit)
        already_public = repo['private'] is False
        if not already_public:
            WRITE_ATTEMPTED = True
            capture(['gh', 'repo', 'edit', REPO, '--visibility', 'public',
                     '--accept-visibility-change-consequences'], 'Repository visibility change', env=gh_env)
        repo, branch = get('repos/' + REPO), get('repos/' + REPO + '/git/ref/heads/main')
        validate_remote(repo, branch, args.commit)
        require(repo['private'] is False, 'Public visibility was not confirmed')
        print(json.dumps({'name': REPO, 'private': False, 'main_sha': args.commit,
                          'status': 'already_public_verified' if already_public else 'published_and_verified'}))
    finally:
        if gh_env is not None:
            gh_env.pop('GH_TOKEN', None)
        token = None


if __name__ == '__main__':
    try:
        main()
    except GateError as error:
        print(json.dumps({'status': 'not_confirmed', 'summary': str(error),
                          'visibility_change_attempted': WRITE_ATTEMPTED}))
        raise SystemExit(1)
    except SystemExit:
        raise
    except BaseException:
        print(json.dumps({'status': 'not_confirmed', 'summary': 'Unexpected failure; no credential details were emitted',
                          'visibility_change_attempted': WRITE_ATTEMPTED}))
        raise SystemExit(1)
