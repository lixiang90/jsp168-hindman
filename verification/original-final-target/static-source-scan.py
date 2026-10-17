#!/usr/bin/env python3
"""Read-only lexical inventory for the prepared final target; never invokes Lean.

Only the explicitly supplied manifest sources are scanned. This is not a Lean
parser, a transitive axiom audit, or kernel replay. Default operation is read-only
and prints a compact report. --detail-output and --compact-output explicitly save
new evidence files; existing outputs are refused without --replace-output.
Example (no Lean/Lake execution):
  python verification/original-final-target/static-source-scan.py \
    --compare-commit 2bd0c12 \
    --detail-output verification-local/final-target-2026-10-17/static-proof-input-scan-2026-10-17.json
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DEFAULT_MANIFEST = ROOT / 'verification-local/final-target-2026-10-17/source-closure.json'
HELPER = ROOT / 'verification/original-upstream-inverse/verify-prepared.py'
strip = runpy.run_path(str(HELPER))['lean_code']
sha = lambda b: hashlib.sha256(b).hexdigest()

parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
parser.add_argument('--manifest', default=str(DEFAULT_MANIFEST))
parser.add_argument('--detail-output', help='Explicit path for all findings/context; confined to repository')
parser.add_argument('--compact-output', help='Explicit path for compact report; confined to repository')
parser.add_argument('--compare-commit', help='Optional Git commit for a read-only comparison of the three local source directories')
parser.add_argument('--replace-output', action='store_true', help='Allow replacing only explicitly requested output files')
parser.add_argument('--lean-source-root', help='Optional installed toolchain src/lean directory; default uses ELAN_HOME or ~/.elan and lean-toolchain')
args = parser.parse_args()

def confined(value):
    path = Path(value)
    if not path.is_absolute():
        path = ROOT / path
    path = path.resolve()
    if not path.is_relative_to(ROOT):
        raise ValueError('Path escapes repository: ' + value)
    return path

MANIFEST = confined(args.manifest)
outputs = {k: confined(v) for k, v in (('detail', args.detail_output), ('compact', args.compact_output)) if v}
if len(set(outputs.values())) != len(outputs):
    raise ValueError('Detail and compact outputs must be distinct')
for path in outputs.values():
    if path == MANIFEST or path == HELPER or path.suffix != '.json':
        raise ValueError('Refusing evidence-input/non-JSON output: ' + str(path))
    if path.exists() and not args.replace_output:
        raise ValueError('Output already exists; choose a new path or explicitly use --replace-output: ' + str(path))

def git(*arguments):
    return subprocess.run(['git', *arguments], cwd=ROOT, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout.strip()

git_head = git('rev-parse', 'HEAD')
comparison = None
source_dirs = ['Hindman168', 'dependencies/openai-finite-szemeredi', 'PrimeNumberTheoremAnd']
if args.compare_commit:
    base_commit = git('rev-parse', '--verify', args.compare_commit + '^{commit}')
    diff = git('diff', '--name-only', base_commit, git_head, '--', *source_dirs)
    comparison = {'base_commit': base_commit, 'head_commit': git_head,
                  'compared_source_directories': source_dirs,
                  'changed_tracked_paths_between_commits': diff.splitlines() if diff else [],
                  'tracked_source_directories_identical_between_commits': not diff}

PRIMARY = ('sorry', 'admit', 'axiom', 'native_decide', 'unsafe', 'extern',
           'implemented_by', 'opaque')
EXTRA = ('sorryAx', 'ofReduceBool', 'ofReduceNat', 'ofReduceInt', 'run_tac',
         'run_elab', 'elab', 'macro', 'initialize', 'builtin_initialize',
         'noncomputable', 'partial', 'meta')
PATTERN = re.compile(r'\b(' + '|'.join(PRIMARY + EXTRA) + r')\b')
OPTION = re.compile(r'\bset_option\s+([A-Za-z_][A-Za-z_0-9.]*)\s+(\S+)')
COMMAND = re.compile(r'#(?:eval|reduce|print|check|run)\b')
OPTIONS = {
    'maxHeartbeats': 'resource_limit',
    'maxRecDepth': 'resource_limit',
    'synthInstance.maxHeartbeats': 'resource_limit',
    'autoImplicit': 'implicit_binder_elaboration',
    'lang.lemmaCmd': 'theorem_command_syntax_alias',
    'linter.style.header': 'header_style_linter',
    'backward.isDefEq.respectTransparency': 'metaprogram_definitional_equality_strategy',
}

def rel(path):
    return path.relative_to(ROOT).as_posix()

def source_path(value):
    path = (ROOT / value).resolve()
    if not path.is_relative_to(ROOT) or path.suffix != '.lean':
        raise ValueError('Invalid source path: ' + value)
    return path

manifest_bytes = MANIFEST.read_bytes()
manifest = json.loads(manifest_bytes)
sources = manifest['sources']
if len(sources) != manifest['local_source_modules']:
    raise ValueError('Manifest source count mismatch')
if set(manifest['local_namespaces']) != {'Hindman168', 'OAI', 'PrimeNumberTheoremAnd'}:
    raise ValueError('Unexpected local namespace scope')
for path in outputs.values():
    if path in {source_path(e['path']) for e in sources.values()}:
        raise ValueError('Output would replace a scanned source')
counts, by_namespace, extra_examples = Counter(), {}, {}
noncomputable_forms = Counter()
set_option_tokens = 0
findings, options, hash_failures, lengths, command_findings = [], [], [], [], []
scanned_hashes = {}
for module, entry in sorted(sources.items()):
    path = source_path(entry['path'])
    data = path.read_bytes()
    digest = sha(data)
    scanned_hashes[module] = digest
    if digest != entry['sha256']:
        hash_failures.append({'module': module, 'expected': entry['sha256'], 'actual': digest})
    if len(data) != entry['bytes']:
        lengths.append({'module': module, 'expected': entry['bytes'], 'actual': len(data)})
    raw = data.decode('utf-8-sig')
    code = strip(raw)
    raw_lines = raw.splitlines()
    set_option_tokens += len(re.findall(r'\bset_option\b', code))
    noncomputable_forms.update(re.findall(r'\bnoncomputable\s+([A-Za-z_][A-Za-z_0-9]*)', code))
    for number, line in enumerate(code.splitlines(), 1):
        context = '\n'.join(raw_lines[max(0, number-2):number+2])
        for match in PATTERN.finditer(line):
            token = match.group(0)
            counts[token] += 1
            namespace = module.split('.')[0]
            by_namespace.setdefault(namespace, Counter())[token] += 1
            item = {'module': module, 'path': entry['path'], 'line': number,
                    'token': token, 'code_line': line.strip(), 'source_context': context}
            if token in PRIMARY or token in ('sorryAx', 'ofReduceBool', 'ofReduceNat', 'ofReduceInt'):
                findings.append(item)
            elif len(extra_examples.setdefault(token, [])) < 10:
                extra_examples[token].append(item)
        for match in COMMAND.finditer(line):
            command_findings.append({'module': module, 'path': entry['path'], 'line': number,
                                     'command': match.group(0), 'code_line': line.strip()})
    for match in OPTION.finditer(code):
        number = code.count('\n', 0, match.start()) + 1
        name, value = match.groups()
        category = OPTIONS.get(name, 'unclassified_option_requires_review')
        if category == 'resource_limit' and not value.isdigit():
            category = 'unclassified_resource_value_requires_review'
        if name == 'autoImplicit' and value != 'false':
            category = 'implicit_binder_elaboration_requires_review'
        options.append({'module': module, 'path': entry['path'], 'line': number,
                        'name': name, 'value': value, 'category': category,
                        'code_line': code.splitlines()[number-1].strip(),
                        'source_context': '\n'.join(raw_lines[max(0, number-2):number+3])})

# Catch source changes during this multi-file read; this is not a filesystem lock.
changed_after_scan = [module for module, entry in sources.items()
                      if sha(source_path(entry['path']).read_bytes()) != scanned_hashes[module]]
head_at_end = git('rev-parse', 'HEAD')
tracked_source_diff = git('diff', '--name-only', git_head, '--', *source_dirs)
tracked_paths = set(git('ls-files', '--', *source_dirs).splitlines())
untracked_scanned_sources = [e['path'] for e in sources.values() if e['path'] not in tracked_paths]
pinned_toolchain = (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip()
toolchain_name = pinned_toolchain.replace('/', '--').replace(':', '---')
lean_source_root = (Path(args.lean_source_root).resolve() if args.lean_source_root else
                    Path(os.environ.get('ELAN_HOME', str(Path.home() / '.elan'))) / 'toolchains' / toolchain_name / 'src/lean')
evidence_paths = [
    lean_source_root / 'Lean/Meta/ExprDefEq.lean',
    ROOT / '.lake/packages/batteries/Batteries/Tactic/Lemma.lean',
    ROOT / '.lake/packages/mathlib/Mathlib/Tactic/Linter/Header.lean',
]
evidence = []
for index, path in enumerate(evidence_paths):
    logical = ({'kind': 'pinned-toolchain-source', 'toolchain': pinned_toolchain,
                'path': 'Lean/Meta/ExprDefEq.lean'} if index == 0 else
               {'kind': 'repository-dependency-source', 'path': rel(path)})
    evidence.append({**logical, 'available': path.is_file(),
                     'sha256': sha(path.read_bytes()) if path.is_file() else None})
summary = {
    'local_source_modules': len(sources),
    'source_counts_by_namespace': manifest['source_counts_by_namespace'],
    'manifest_source_hashes_match_at_scan': not hash_failures,
    'manifest_source_byte_lengths_match_at_scan': not lengths,
    'all_scanned_sources_unchanged_at_end': not changed_after_scan,
    'git_head_unchanged_during_scan': git_head == head_at_end,
    'tracked_source_directory_worktree_diff_at_end': tracked_source_diff.splitlines() if tracked_source_diff else [],
    'scanned_source_paths_not_tracked_at_head': untracked_scanned_sources,
    'primary_token_occurrences': {token: counts[token] for token in PRIMARY},
    'supplemental_token_occurrences': {token: counts[token] for token in EXTRA},
    'set_option_occurrences': len(options),
    'set_option_token_occurrences': set_option_tokens,
    'all_set_option_tokens_parsed': set_option_tokens == len(options),
    'autoImplicit_set_option_occurrences': sum(x['name'] == 'autoImplicit' for x in options),
    'noncomputable_following_syntax_token_counts': dict(sorted(noncomputable_forms.items())),
    'set_options_by_name_value': dict(sorted(Counter(x['name'] + ' ' + x['value'] for x in options).items())),
    'set_options_by_category': dict(sorted(Counter(x['category'] for x in options).items())),
    'unclassified_options': sum('requires_review' in x['category'] for x in options),
    'source_hash_mismatches': hash_failures,
    'source_byte_length_mismatches': lengths,
    'changed_after_scan': changed_after_scan,
    'direct_external_boundary_unique_modules_excluded': manifest['external_boundary_unique_modules'],
    'direct_external_boundary_import_edges_excluded': manifest['external_boundary_import_edges'],
}
report = {
    'schema': 'hindman.final-target-static-proof-input-scan.v1',
    'generated_utc': datetime.now(timezone.utc).isoformat(),
    'status': 'static lexical scan only; no Lean or Lake commands executed',
    'target': manifest['target'],
    'manifest_path': rel(MANIFEST), 'manifest_file_sha256': sha(manifest_bytes),
    'manifest_source_inventory_sha256': manifest['source_inventory_sha256'],
    'git_head_at_start': git_head, 'git_head_at_end': head_at_end,
    'optional_git_source_comparison': comparison,
    'scanner_path': rel(Path(__file__).resolve()),
    'scanner_sha256': sha(Path(__file__).read_bytes()),
    'comment_string_stripper_path': rel(HELPER), 'comment_string_stripper_sha256': sha(HELPER.read_bytes()),
    'method': 'Manifest paths confined to repository; exact bytes SHA256 and lengths; strip nested block comments, line comments, and double-quoted strings preserving lines; whole-word token scan; scan every set_option name/value; rehash every source at end.',
    'summary': summary,
    'primary_and_reduction_oracle_findings': findings,
    'set_options': options,
    'supplemental_counts_by_namespace': {k: dict(sorted(v.items())) for k, v in sorted(by_namespace.items())},
    'supplemental_examples_max_10_each': extra_examples,
    'diagnostic_or_evaluation_commands': command_findings,
    'option_classification': {
        'resource_limit': 'Changes elaboration recursion/time allowance, including 0 meaning unlimited; does not itself introduce proof constants or bypass kernel checking.',
        'implicit_binder_elaboration': 'autoImplicit=false disables automatic undeclared implicit binders; it does not add axioms. No assumption that it is present.',
        'theorem_command_syntax_alias': 'Batteries lang.lemmaCmd enables lemma as a synonym for theorem; elabLemma rewrites the command and calls ordinary declaration elaboration.',
        'header_style_linter': 'Mathlib header linter flag; controls style checks, not the proof kernel.',
        'metaprogram_definitional_equality_strategy': 'Lean.Meta.ExprDefEq backward.isDefEq.respectTransparency=false restores older implicit-argument transparency bump to .default during meta-level unification. It affects proof elaboration strategy, not logical axioms or kernel transparency rules. Requires actual elaboration/kernel validation; the option is not itself evidence of unsoundness.',
    },
    'option_implementation_evidence': evidence,
    'limitations': [
        'Lexical scanner, not a full Lean parser; stripping comments/strings and matching tokens is a publication input review aid, not a proof of absence of all trust mechanisms.',
        'Only manifest-listed local sources in Hindman168/OAI/PrimeNumberTheoremAnd are scanned. External Mathlib/Lean/Batteries transitive source closure is not scanned by this report.',
        'Absence of the scanned constructs does not rule out hidden mathematical hypotheses or automatically generated declarations; CheckEndpoint type locks and the full all-declarations transitive-axiom audit remain separate requirements.',
        'noncomputable permits definitions whose executable code is not required (for example, definitions using classical choice); it does not itself add axioms and is not a placeholder. Actual dependencies must be assessed by the separate axiom audit.',
        'Opaque declarations are not automatically unsound; unsafe/runtime implementations require context and actual proof-dependency analysis. Counts here report syntax occurrences only.',
        'This script does not execute Lean, Lake, axiom auditing, or leanchecker, and does not establish that the final target builds or is proved.',
    ],
    'lean_executed': False, 'lake_executed': False, 'axiom_audit_executed': False,
    'kernel_replay_executed': False, 'full_target_proved_by_this_scan': False,
}
compact = {k: v for k, v in report.items() if k not in {
    'primary_and_reduction_oracle_findings', 'set_options',
    'supplemental_examples_max_10_each', 'diagnostic_or_evaluation_commands'}}
compact['primary_and_reduction_oracle_findings'] = findings
compact['diagnostic_or_evaluation_command_counts'] = dict(sorted(Counter(x['command'] for x in command_findings).items()))
compact['detail_report'] = None
if 'detail' in outputs:
    detail = outputs['detail']
    detail.parent.mkdir(parents=True, exist_ok=True)
    detail.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    compact['detail_report'] = {'path': rel(detail), 'sha256': sha(detail.read_bytes())}
if 'compact' in outputs:
    output = outputs['compact']
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(compact, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps(compact, indent=2, ensure_ascii=False))
