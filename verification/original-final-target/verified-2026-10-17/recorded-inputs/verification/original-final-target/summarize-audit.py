#!/usr/bin/env python3
"""Read-only parser for actual all-declaration Lean audit logs.

Usage: python summarize-audit.py MANIFEST LEAN_STDOUT [--output NEW_JSON]
No Lean/Lake execution. A valid log does not by itself attest compilation,
source/artifact identity, process exit, or fresh kernel replay. --output writes
only a new explicit report inside this repository; default is read-only.
"""
import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}
ANSI = re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')
# CLI info messages can be bare or carry a source-position prefix.
PREFIX = re.compile(r'^\s*(?:(?:.*?:\d+:\d+:\s*)?info:\s*)?')
MARKER = re.compile(r'^AUDIT\s+(DECL|MODULE|COMPLETE)\s*:')
MOD = r'([A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*)'
DECL = re.compile(r'^AUDIT\s+DECL\s*:\s*' + MOD + r'\s*;\s*(.+?)\s*;\s*axioms\s*:\s*\[([^\[\]]*)\]\s*$', re.S)
MODULE = re.compile(r'^AUDIT\s+MODULE\s*:\s*' + MOD + r'\s*;\s*all\s+(\d+)\s+declaration\s+records\s+checked\s*$', re.S)
COMPLETE = re.compile(r'^AUDIT\s+COMPLETE\s*:\s*(\d+)\s+local\s+modules\s*;\s*(\d+)\s+unique\s+declarations\s*;\s*(\d+)\s+records\s*;\s*only\s+standard\s+three\s+axioms\s*$', re.S)
ERROR = re.compile(r'^\s*(?:.*?:\d+:\d+:\s*)?error\s*:')


def canonical_name(text):
    """Ignore formatter whitespace outside escaped Lean identifier components."""
    result, quoted = [], False
    for ch in text.strip():
        if ch == '«':
            quoted = True
        if quoted or not ch.isspace():
            result.append(ch)
        if ch == '»':
            quoted = False
    return ''.join(result)


def parse_audit(manifest, lines):
    """Pure record parser; synthetic self-tests use this without real target logs."""
    targets = set(manifest.get('sources', {}))
    errors = []
    if not targets or manifest.get('local_source_modules') != len(targets):
        errors.append('Invalid/empty manifest local source module set/count')
    counts = Counter()
    names_by_module = defaultdict(set)
    name_modules = defaultdict(set)
    module_footer = {}
    axioms_used = Counter()
    complete = []
    record_kinds = Counter()
    pending, start_line = [], None
    total_records = 0
    unrelated_lines = 0

    def consume(text, number):
        nonlocal total_records
        if complete:
            errors.append(f'Line {number}: AUDIT record after AUDIT COMPLETE')
        kind = MARKER.match(text).group(1)
        record_kinds[kind] += 1
        pattern = {'DECL': DECL, 'MODULE': MODULE, 'COMPLETE': COMPLETE}[kind]
        match = pattern.fullmatch(text)
        if match is None:
            errors.append(f'Line {number}: malformed/incomplete AUDIT {kind} record')
            return
        if kind == 'DECL':
            module, raw_name, raw_axioms = match.groups()
            name = canonical_name(raw_name)
            axioms = [canonical_name(a) for a in raw_axioms.split(',')] if raw_axioms.strip() else []
            total_records += 1
            counts[module] += 1
            if module not in targets:
                errors.append(f'Line {number}: declaration from unexpected module {module}')
            if module in module_footer:
                errors.append(f'Line {number}: declaration after its module footer: {module}')
            if not name:
                errors.append(f'Line {number}: empty declaration name')
            if name in names_by_module[module]:
                errors.append(f'Line {number}: duplicate declaration record in {module}: {name}')
            names_by_module[module].add(name)
            name_modules[name].add(module)
            if len(set(axioms)) != len(axioms):
                errors.append(f'Line {number}: duplicate axiom entries for {name}')
            for axiom in axioms:
                axioms_used[axiom] += 1
                if axiom not in ALLOW:
                    errors.append(f'Line {number}: unapproved axiom {axiom!r} for {module}: {name}')
        elif kind == 'MODULE':
            module, count = match.groups()
            if module not in targets:
                errors.append(f'Line {number}: unexpected module footer {module}')
            if module in module_footer:
                errors.append(f'Line {number}: duplicate module footer {module}')
            module_footer[module] = int(count)
        else:
            complete.append({'modules': int(match[1]), 'unique_declarations': int(match[2]),
                             'records': int(match[3]), 'line': number})

    for number, raw in enumerate(lines, 1):
        line = ANSI.sub('', raw.rstrip('\r\n')).lstrip('\ufeff')
        if ERROR.match(line):
            errors.append(f'Line {number}: Lean error diagnostic: {line.strip()}')
        candidate = PREFIX.sub('', line, count=1)
        if MARKER.match(candidate):
            if pending:
                consume('\n'.join(pending), start_line)
            pending, start_line = [candidate], number
        elif pending:
            pending.append(line)
        else:
            if candidate.startswith('AUDIT'):
                errors.append(f'Line {number}: unrecognized AUDIT marker')
            if line.strip():
                unrelated_lines += 1
        if pending:
            text = '\n'.join(pending)
            kind = MARKER.match(text).group(1)
            if {'DECL': DECL, 'MODULE': MODULE, 'COMPLETE': COMPLETE}[kind].fullmatch(text):
                consume(text, start_line)
                pending, start_line = [], None
            elif len(text) > 1024 * 1024:
                errors.append(f'Line {start_line}: oversized incomplete AUDIT record')
                pending, start_line = [], None
    if pending:
        consume('\n'.join(pending), start_line)

    missing = sorted(targets - set(module_footer))
    extra = sorted((set(module_footer) | set(counts)) - targets)
    if missing:
        errors.append(f'Missing module footers: {len(missing)}')
    if extra:
        errors.append(f'Unexpected modules: {len(extra)}')
    per_module = {}
    for module in sorted(targets | set(module_footer) | set(counts)):
        reported = module_footer.get(module)
        actual = counts[module]
        matched = reported is not None and reported == actual
        per_module[module] = {'declaration_records': actual,
                              'unique_declaration_names': len(names_by_module[module]),
                              'reported_declaration_records': reported,
                              'count_matches': matched}
        if reported is not None and reported != actual:
            errors.append(f'Module count mismatch {module}: log footer={reported}, parsed={actual}')
    unique = len(name_modules)
    if len(complete) != 1:
        errors.append(f'Expected exactly one AUDIT COMPLETE, found {len(complete)}')
    else:
        expected = {'modules': len(targets), 'unique_declarations': unique, 'records': total_records}
        for field, value in expected.items():
            if complete[0][field] != value:
                errors.append(f'Complete {field} mismatch: footer={complete[0][field]}, parsed={value}')
    if total_records == 0:
        errors.append('Empty declaration audit')
    return {
        'schema': 'hindman.all-declarations-audit-log-summary.v1',
        'scope': 'Parsed supplied log only; not compilation, process-exit, artifact binding, or kernel replay evidence.',
        'target': manifest.get('target'), 'passed': not errors,
        'manifest_modules': len(targets), 'module_footers': len(module_footer),
        'declaration_records': total_records, 'unique_declarations': unique,
        'record_kinds': dict(record_kinds), 'complete_records': complete,
        'axiom_allowlist': sorted(ALLOW), 'axiom_declaration_use_counts': dict(sorted(axioms_used.items())),
        'missing_modules': missing, 'unexpected_modules': extra,
        'names_shared_between_modules': sum(len(modules) > 1 for modules in name_modules.values()),
        'unrelated_nonempty_lines': unrelated_lines, 'errors': errors, 'per_module': per_module,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest', type=Path)
    parser.add_argument('log', type=Path)
    parser.add_argument('--output', type=Path, help='New report file within repository; existing files are refused')
    args = parser.parse_args()
    manifest_path, log_path = args.manifest.resolve(), args.log.resolve()
    output = args.output.resolve() if args.output else None
    if output and (not output.is_relative_to(ROOT) or output.exists() or output in {manifest_path, log_path}):
        parser.error('Output must be a new file within this repository')
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    digest = hashlib.sha256()
    before = log_path.stat()
    bytes_read = 0
    def read_lines():
        nonlocal bytes_read
        with log_path.open('rb') as stream:
            for raw in stream:
                digest.update(raw)
                bytes_read += len(raw)
                yield raw.decode('utf-8')
    report = parse_audit(manifest, read_lines())
    after = log_path.stat()
    if (before.st_size, before.st_mtime_ns) != (after.st_size, after.st_mtime_ns) or bytes_read != after.st_size:
        report['errors'].append('Log changed while being parsed; retry only after the audit process has finished')
        report['passed'] = False
    report.update(generated_utc=datetime.now(timezone.utc).isoformat(),
                  manifest_sha256=hashlib.sha256(manifest_bytes).hexdigest(),
                  source_inventory_sha256=manifest.get('source_inventory_sha256'),
                  log_sha256=digest.hexdigest(), log_bytes=bytes_read,
                  parser_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
        display = {k: v for k, v in report.items() if k != 'per_module'}
        display['report'] = output.relative_to(ROOT).as_posix()
        display['report_sha256'] = hashlib.sha256(output.read_bytes()).hexdigest()
    else:
        display = report
    print(json.dumps(display, indent=2, ensure_ascii=False))
    return 0 if report['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
