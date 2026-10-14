"""Register and audit the Hilbert projection and Ramsey energy increment against its saved baseline."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-projection-gap-energy'
OLD = 'round-native-lie-layer-compact'
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/NestedProjectionEnergy.lean', 'Hindman168/RamseyEnergySelection.lean', 'Hindman168/RamseyProjectionSelection.lean']
COMPONENTS = ["Genuine nested orthogonal projections satisfy the exact squared-distance/energy-difference identity, energy monotonicity and the paper's 2 epsilon fine-projection error bound from coarse approximation.", 'Pythagorean decomposition proves that any representative-preserving clipping which contracts distance to the original vector also contracts distance to its orthogonal projection. Density then supplies clipped representatives with any prescribed positive accuracy and the stated clipping predicate.', 'A uniform finite Ramsey bound is proved for simultaneously binned [0,1] energies with arbitrary finite labels and every tuple cardinality up to K. The finite bound is selected BEFORE all energy data, depends only on labels/K/desired size/bin width, and gives strict bin-width closeness.', 'The uniform energy selector is instantiated on genuine Hilbert-space projection energies of unit-bounded vectors, then yields the 2 epsilon model-error estimate whenever the selected pair has nested subspaces and the same vector. No actual nilsequence space or ultralimit is assumed to have been constructed by this abstract lemma.']
REMAINING = "Original native lower-central geometry, specified-lattice quotients and canonical cube compactness remain proved. The original-law model-error testing interface has no supplied layer-compactness premise. The abstract Hilbert-space energy identity, clipping approximation and uniform finite Ramsey gap-energy selection are NOW PROVED with the correct bound-before-data quantifiers. The actual ultrafilter/completed Hilbert space, piecewise nilsequence closed spans, their nesting and closure under representing operations/clipping still must be constructed and plugged into these lemmas, with finite common complexity and the paper's padding/principal tuple indexing. Remaining full-target work also includes Calibration/Alignment, subgroup inverse inputs, actual coloring/arithmetic data and ordered positive rapidly separated monochromatic witnesses, and quantitative degree/denominator bounds where required. The original model, group, Gamma and StrongConjecture statement remain unchanged. StrongConjecture and the prize target remain unproved. No unavoidable blocker is established; publication, PR and prize application remain pending."


def declarations():
    return {p: old.declarations(p) for p in MODULES}


def register():
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 930
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for values in ds.values() for _, name in values]
    assert len(names) == len(set(names)) == 12
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 12
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 930, 'modules': MODULES,
        'names': names, 'theorem_count': 12, 'declarations': ds})
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
    assert len(own) == 915 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for ds in declarations().values() for _, n in ds]
    assert names == registration['names'] and len(names) == 12
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
    assert len(registered) == len(set(registered)) == len(actual) == 4475
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert all(actual[n] == v for n, v in previous.items())
    assert all(v <= old.ALLOWED for v in actual.values())
    assert {n for n, v in actual.items() if not v} == old.AXIOM_FREE
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
    assert len(files) == len({f['path'] for f in files}) == 933
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=12, new_definitions=0, new_axiom_reports=12, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True, full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. The preceding audit was rechecked before edits. All 930 baseline hashes are checked at registration. Only root imports and axiom registry change among retained source/config files; original statements, geometry, arithmetic and all retained proofs stay intact.', 'The source route is section 05_prediction.tex, nested-spaces equation and Ramsey selection of gap energies lemma. The new declarations prove their Hilbert identities and uniform selection mechanism, not the existence of the actual ultralimit or nilsequence spaces.', 'The nested projection identity uses the genuine mathlib orthogonal projection, its composition for U <= V, and the orthogonal-complement Pythagorean decomposition. The sign is fine-space energy minus coarse-space energy. Nonnegativity is proved, not assumed. The 2 epsilon bound uses the same vector and a model lying in the coarse space.', 'The clipping lemma compares squared distances to the original vector and cancels the SAME perpendicular residual in two exact Pythagorean identities. The representative existence theorem explicitly assumes density, closure under clipping, clipping contraction and its output predicate. These are obligations for the actual representing families and are not hidden in a claimed nilsequence construction.', 'Natural floor bins handle both endpoints of [0,1], including energy=1. The finite palette has floor(1/delta)+1 bins per label. Equal bins imply STRICT distance < delta via lower and upper floor inequalities and delta>0. No unjustified bound or unbounded color set enters Ramsey.', 'The joint palette is the finite function type from labels to bins. The retained finite size-homogeneous Ramsey theorem selects N before the arbitrary energy function. All equal-cardinality subsets up to K and all labels share the estimate. Empty label types and size-zero cases are permitted without fabricating colors.', 'Projection energy lies in [0,1] by the genuine operator contraction and the input vector norm bound. Selection uses delta=epsilon^2. The model-selection theorem explicitly requires equal vectors and nested spaces for a selected pair, preserving the same-vector condition required by the energy identity. Actual tail/padding tuple decoding remains to be supplied.', 'No full Calibration/Alignment, ultrafilter Hilbert completion, common-complexity actual nilsequence model, inverse theorem or final StrongConjecture is claimed. The task remains active, with no unavoidable blocker established.'], new_modules=MODULES, verified=summary, remaining=REMAINING)
    manifest = dict(baseline)
    manifest.update(files=files, hindman_module_count=915, pntplus_module_count=9,
        selected_axiom_report_count=4475, source_scan_module_count=924,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=3, new_theorem_count=12,
            new_selected_report_count=12, retained_proof_sources_changed=False,
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
