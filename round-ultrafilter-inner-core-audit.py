"""Register and audit the original-law ultrafilter Hilbert construction against its saved baseline."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-ultrafilter-inner-core'
OLD = 'round-projection-gap-energy'
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/BoundedHilbertFamilies.lean', 'Hindman168/UltrafilterInnerCore.lean', 'Hindman168/UltrafilterHilbertCompletion.lean', 'Hindman168/UltrafilterHilbertEmbedding.lean', 'Hindman168/FiniteMassL2Space.lean', 'Hindman168/FiniteMassUltrafilterHilbert.lean']
COMPONENTS = ['Uniformly norm-bounded families in VARYING real seminormed inner product spaces form an actual vector submodule. Their pairings are uniformly bounded by Cauchy-Schwarz and have actual real ultrafilter limits by compactness.', 'The actual ultralimit pairing is proved symmetric, positive semidefinite, additive and real-linear. Its genuine seminorm supplies a separated complete real Hilbert space, with a dense linear canonical map preserving the ultralimit inner product.', 'The canonical images are equal IFF squared coordinate distances tend to zero along the specified ultrafilter. Uniform coordinate norm bounds pass to the completion. The canonical free hyperfilter extends atTop, so ordinary scalar pairing limits give the same Hilbert pairing.', 'Original nonnegative finitely supported masses now supply actual coordinate L2 seminorms: squared norm is exactly the original weighted expectation of the square. Probability masses and supportwise bounded functions give uniformly bounded coordinate vectors. No counting law, normalization or deletion of zero-weight coordinates is substituted.', 'Instantiating the completed Hilbert construction on ANY original sequence of nonnegative finite masses gives pairing exactly equal to the ultralimit of the original weighted expectations. Equality of vectors is exactly vanishing original weighted squared distance; ordinary pairing limits pass to the fixed free-hyperfilter Hilbert space.']
REMAINING = "Original native lower-central geometry, specified-lattice quotients and cube compactness remain proved. The abstract Hilbert energy identities, clipping approximation and uniform finite Ramsey selection remain proved. The AMBIENT Hilbert construction is NOW PROVED: actual uniformly L2-bounded families for varying original nonnegative finite laws, actual ultrafilter pairing, zero-distance identification and separated complete Hilbert space with dense linear realization, original expectation pairing and ordinary-limit compatibility. Next construct actual bounded-complexity piecewise nilsequence families inside this space, their closed spans, nesting and closure under representing operations/clipping, then instantiate projection selection with finite common complexity and the paper's padding/principal tuple indexing. Remaining full-target work also includes Calibration/Alignment, subgroup inverse inputs, actual coloring/arithmetic data and ordered positive rapidly separated monochromatic witnesses, and quantitative degree/denominator bounds where required. Original model, group, Gamma, sampling laws and StrongConjecture remain unchanged. StrongConjecture and the prize target remain unproved. No unavoidable blocker is established; publication, PR and prize application remain pending."


def declarations():
    return {p: old.declarations(p) for p in MODULES}


def register():
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 933
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for values in ds.values() for _, name in values]
    assert len(names) == len(set(names)) == 42
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 21
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 933, 'modules': MODULES,
        'names': names, 'theorem_count': 21, 'declarations': ds})
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
    assert len(own) == 921 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for ds in declarations().values() for _, n in ds]
    assert names == registration['names'] and len(names) == 42
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
    assert len(registered) == len(set(registered)) == len(actual) == 4517
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
    assert len(files) == len({f['path'] for f in files}) == 939
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=21, new_definitions=10, new_instances=11, new_axiom_reports=42, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True, full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. Previous audit rechecked before edits. All 933 retained source/config hashes checked before registration; only root imports and registry change. No retained proof, original statement, model, lattice, law, pinned dependency or attributed source is modified.', 'The source route is the actual Hilbert-space paragraph of 05_prediction.tex immediately before nested-spaces. The coordinate spaces can vary with w and may be SEMInormed, permitting original zero-mass coordinates. Every family has one finite norm bound valid for all w; this is not an unbounded Cartesian product.', 'Cauchy-Schwarz bounds each scalar pairing by the product of two uniform norm bounds. The image ultrafilter lies in a compact real interval, giving genuine convergence to limUnder. Bilinearity and positivity use convergence and Hausdorff uniqueness, rather than an unproved limit functional or arbitrary choice of scalar values.', 'Positive semidefiniteness is established before quotient/completion. The UltrafilterFamily type synonym deliberately prevents coordinatewise product topology inference. Its seminorm comes ONLY from the proved ultralimit core. The complete space inherits this exact uniform structure, and inner preservation is checked explicitly by Completion.inner_coe.', 'The canonical map is a genuine real linear map with dense range. Its squared norm equals the ultralimit self-pairing. The squared-distance limit proves both directions of the equality/zero-distance equivalence, so zero-norm families are identified and distinct vectors cannot survive with zero norm. This is the separated completion required in the paper.', 'The fixed Filter.hyperfilter on natural numbers extends atTop by the library theorem Nat.hyperfilter_le_atTop. All ordinary scalar pairing limits therefore agree with the chosen free-ultrafilter pairing. No false claim of ordinary convergence is made from ultrafilter convergence.', 'FiniteMassL2 uses exactly expectation mu (f*g), with nonnegativity checked for the given mass. The squared norm equals expectation mu (f^2). The probability-bound theorem uses total mu=1 only for the uniform norm estimate; the space construction does not normalize mass. The function bound is needed only on the actual support.', 'FiniteMassUltrafilterHilbert instantiates the actual completed Hilbert space on the original mass family, with pairing exactly the original expectation ultralimit and equality exactly vanishing original mean squared distance. These identities certify the intended law, not a merely isomorphic unrelated probability model.', 'Actual bounded-complexity nilsequence representing families and their closed-span nesting, clipping stability, finite complexity bounds, tuple selection, Calibration/Alignment and StrongConjecture remain to be proved. No unavoidable blocker, full-target claim, publication or prize submission is asserted.'], new_modules=MODULES, verified=summary, remaining=REMAINING)
    manifest = dict(baseline)
    manifest.update(files=files, hindman_module_count=921, pntplus_module_count=9,
        selected_axiom_report_count=4517, source_scan_module_count=930,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=6, new_theorem_count=21,
            new_selected_report_count=42, retained_proof_sources_changed=False,
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
