"""Register and audit the actual product quotient and representation increment against its saved baseline."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-indexed-energy'
OLD = 'round-native-hilbert-span'
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/EnergyTupleEncoding.lean', 'Hindman168/IndexedEnergySelection.lean', 'Hindman168/IndexedProjectionSelection.lean']
COMPONENTS = ['The actual increasing energy tuple T,l,i is encoded by insert i (insert l T). With every tail entry below l<i, its maximum recovers i, the maximum after deleting i recovers l, and deleting both recovers exactly T. Its cardinality is T.card+2 and subset membership is preserved.', 'Uniform finite Ramsey selection now applies to exact tail-gap-pivot energy data. The master bound is chosen before all bounded energy data. On the homogeneous set, energies with the same T,i and different valid gaps l,k differ by less than delta, simultaneously for all finite labels.', 'Projection selection supports a different real Hilbert space for every pivot i. The two compared tuples use exactly the same x(T,i,a) and pivot space, so no equality between targets from different tuples is postulated. Nested spaces and coarse epsilon approximants give the fine projected residual bound 2 epsilon.']
REMAINING = 'Native geometry, Hilbert realization, native finite product closure, actual clipped dense approximation and its conditional fine residual estimate remain proved. Exact tail-gap-pivot tuple encoding and uniform indexed Ramsey energy/projection selection are now proved, including pivot-dependent Hilbert spaces and the same target vector in both compared energies. Next extract alternating padding/principal indices from the homogeneous set, instantiate the native spaces and original block laws, and assemble simultaneous actual representatives with common finite bounds. Calibration/Alignment, subgroup inverse inputs, actual coloring/arithmetic extraction, ordered positive rapidly separated monochromatic witnesses and required quantitative bounds remain. Original StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'


def declarations():
    return {p: old.declarations(p) for p in MODULES}


def register():
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 960
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for values in ds.values() for _, name in values]
    assert len(names) == len(set(names)) == 10
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 6
    root, registry = read('Hindman168.lean'), read('Verification.lean')
    for path in MODULES:
        line = 'import ' + path[:-5].replace('/', '.')
        assert line not in root.splitlines()
        root += '\n' + line + '\n'
    for name in names:
        line = '#print axioms ' + name
        assert line not in registry.splitlines()
        registry += '\n' + line + '\n'
    Path('Hindman168.lean').write_text(root, encoding='utf-8')
    Path('Verification.lean').write_text(registry, encoding='utf-8')
    write(PREFIX + '-registration.json', {'baseline_hash_count': 960, 'modules': MODULES,
        'names': names, 'theorem_count': 6, 'declarations': ds})
    print(json.dumps({'registered': len(names), 'modules': len(MODULES)}))


def run_build(kind):
    command = ['lake', 'build'] if kind == 'build' else ['lake', 'env', 'lean', 'Verification.lean']
    if kind == 'kernel':
        result = obj(PREFIX + '-build-result.json')
        assert result['terminal'] and result['exit_code'] == 0
        assert result['log_sha256'] == digest(PREFIX + '-build.txt')
    log = PREFIX + ('-build.txt' if kind == 'build' else '-axioms.txt')
    start = time.monotonic()
    with open(log, 'wb') as stream:
        result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    record = dict(command=command, exit_code=result.returncode, terminal=True,
                  elapsed_seconds=time.monotonic() - start, log_sha256=digest(log))
    write(PREFIX + '-' + kind + '-result.json', record)
    print(json.dumps(record))
    if result.returncode:
        print(read(log)[-16000:])
        sys.exit(result.returncode)


def check():
    baseline = obj(PREFIX + '-baseline.json')
    registration = obj(PREFIX + '-registration.json')
    changed = [f['path'] for f in baseline['files'] if digest(f['path']) != f['sha256']]
    assert changed == ['Hindman168.lean', 'Verification.lean']
    own = sorted(Path('Hindman168').glob('*.lean'))
    pnt = sorted(Path('PrimeNumberTheoremAnd').rglob('*.lean'))
    assert len(own) == 945 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for ds in declarations().values() for _, n in ds]
    assert names == registration['names'] and len(names) == 10
    for p in own + pnt + [Path('Hindman168.lean'), Path('Verification.lean')]:
        code = old.lean_code(read(p))
        assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|implemented_by)\b', code), p
        assert not re.search(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(?:axiom|unsafe)\b', code, re.M), p
    for p in MODULES:
        assert not re.search(r'\b(?:set_option|setOptions)\b', old.lean_code(read(p)))
        olean = Path('.lake/build/lib/lean') / Path(p).with_suffix('.olean')
        assert olean.stat().st_mtime_ns >= Path(p).stat().st_mtime_ns
    for kind, log in [('build', '-build.txt'), ('kernel', '-axioms.txt')]:
        result = obj(PREFIX + '-' + kind + '-result.json')
        assert result['terminal'] and result['exit_code'] == 0
        assert result['log_sha256'] == digest(PREFIX + log)
        assert result['command'] == (['lake', 'build'] if kind == 'build' else ['lake', 'env', 'lean', 'Verification.lean'])
        assert not re.search(r'(?:error:|warning:)', read(PREFIX + log))
    jobs = re.findall(r'Build completed successfully \((\d+) jobs\)\.', read(PREFIX + '-build.txt'))
    assert len(jobs) == 1 and int(jobs[0]) >= baseline['build_job_count'] + len(MODULES)
    previous, actual = old.reports(OLD + '-axioms.txt'), old.reports(PREFIX + '-axioms.txt')
    assert obj(OLD + '-kernel-result.json')['log_sha256'] == digest(OLD + '-axioms.txt')
    registered = re.findall(r'^#print axioms (\S+)', old.lean_code(read('Verification.lean')), re.M)
    assert len(registered) == len(set(registered)) == len(actual) == 4645
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert all(actual[n] == v for n, v in previous.items())
    assert all(v <= old.ALLOWED for v in actual.values())
    assert {n for n, v in actual.items() if not v} == old.AXIOM_FREE | {'Hindman168.intervalResidueParent'}
    assert old.run(['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD']) == baseline['mathlib_commit']
    assert old.run(['git', '-C', '../reference-pntplus', 'rev-parse', 'HEAD']) == baseline['pntplus_commit']
    lean = old.run(['lake', 'env', 'lean', '--version'])
    assert 'version 4.32.2,' in lean and 'f3b06c705e6c85f5314019d5d3baab0fec5b580c' in lean
    fixed = obj(OLD + '-preprint-local-check.json')
    assert fixed['fixed_openai_math_commit'] == baseline['openai_math_commit']
    for section in fixed['sections']:
        data = (Path('E:/codex-build/math') / section['path']).read_bytes().replace(b'\r\n', b'\n')
        pinned = subprocess.run(['git', '-C', 'E:/codex-build/math', 'show',
            fixed['fixed_openai_math_commit'] + ':' + section['path']], stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, check=True).stdout.replace(b'\r\n', b'\n')
        assert data == pinned and hashlib.sha256(data).hexdigest() == section['normalized_sha256']
    files = [{'path': f['path'], 'sha256': digest(f['path'])} for f in baseline['files']]
    files += [{'path': p, 'sha256': digest(p)} for p in MODULES]
    assert len(files) == len({f['path'] for f in files}) == 963
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=6, new_definitions=4, new_instances=0, new_axiom_reports=10, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True, full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. Previous round rechecked before editing. All 960 retained hashes checked at registration; only root imports and axiom registry change among baseline files. Original statements, original laws, dependencies and fixed source remain unchanged.', 'The paper energy-selection argument colors increasing tuples with tail T followed by gap l and pivot i. Encoding by a finite set is valid because all tail entries precede l<i. Explicit decoding, cardinality and subset theorems establish the bridge to the finite-set Ramsey theorem.', 'A sup on natural numbers defines the total decoder even on empty or singleton sets. Invalid tuples cause no problem: the energy function is globally bounded, while decoding identities are used only for valid tuples. No assumption that an arbitrary finite set has two distinct largest elements is made.', 'The compared finite sets both have cardinality T.card+2. Their recovered tails and pivots coincide exactly, even when l=k. Both gap entries and the pivot belong to the selected set. This rules out the erroneous comparison of projections of unrelated target vectors.', 'The uniform master bound is selected before energy data, projection spaces and vectors. The finite labels are jointly colored, and energy bin width is epsilon squared. The projection variant allows genuinely different Hilbert spaces at different pivots.', 'The fine residual theorem explicitly requires the relevant space inclusion and coarse approximation. It derives the actual energy bound from the indexed homogeneous set and applies the previously proved projection identity. It does not yet instantiate the native original-law spaces or extract alternating padding indices.', 'All four definitions and six theorems are individually kernel-audited. Full target, Calibration/Alignment, final arithmetic extraction, publication and prize submission remain uncompleted.'], new_modules=MODULES, verified=summary, remaining=REMAINING)
    manifest = dict(baseline)
    manifest.update(files=files, hindman_module_count=945, pntplus_module_count=9,
        selected_axiom_report_count=4645, source_scan_module_count=954,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=3, new_theorem_count=6,
            new_selected_report_count=10, retained_proof_sources_changed=False,
            root_and_registry_changed=True, review_file=PREFIX+'-review.json', remaining=REMAINING))
    manifest['proved_components'] = baseline['proved_components'] + COMPONENTS
    audit = read('AUDIT.txt')
    marker = 'Remaining proof work:'
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline['last_round']['remaining']
    note = '\n2026-10-10 ' + PREFIX + ': PROGRESS. ' + ' '.join(COMPONENTS) + '\n'
    note += json.dumps(summary) + '\nReview: ' + PREFIX + '-review.json\n\n'
    Path('AUDIT.txt').write_text(audit.split(marker, 1)[0]+note+marker+'\n'+REMAINING+'\n', encoding='utf-8')
    Path('BUILD-EVIDENCE.txt').write_bytes(b'=== COMPLETE BUILD OUTPUT ===\n' +
        Path(PREFIX+'-build.txt').read_bytes()+b'\n=== COMPLETE AXIOM OUTPUT ===\n'+
        Path(PREFIX+'-axioms.txt').read_bytes()+b'\n')
    write(PREFIX+'-review.json', review)
    write('verification-manifest.json', manifest)
    write(PREFIX+'-preprint-local-check.json', fixed)
    write(PREFIX+'-checks.json', summary)
    print(json.dumps(summary))


def recheck():
    _, files, summary, _ = check()
    manifest = obj('verification-manifest.json')
    assert manifest['files'] == files and manifest['last_round']['remaining'] == REMAINING
    assert obj(PREFIX+'-review.json')['verified'] == summary
    assert read('AUDIT.txt').split('Remaining proof work:', 1)[1].strip() == REMAINING
    assert Path('BUILD-EVIDENCE.txt').read_bytes() == b'=== COMPLETE BUILD OUTPUT ===\n' + \
        Path(PREFIX+'-build.txt').read_bytes()+b'\n=== COMPLETE AXIOM OUTPUT ===\n'+ \
        Path(PREFIX+'-axioms.txt').read_bytes()+b'\n'
    print(json.dumps(summary))


if __name__ == '__main__':
    sys.stdout.reconfigure(encoding='utf-8')
    mode = sys.argv[1]
    if mode == 'register': register()
    elif mode in {'build', 'kernel'}: run_build(mode)
    elif mode == 'record': record()
    elif mode == 'recheck': recheck()
    else: raise ValueError(mode)
