"""Register and audit the actual piece refinement and Hilbert clipping increment against its saved baseline."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-piece-refinement-hilbert'
OLD = 'round-ultrafilter-inner-core'
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/NilPieceRefinement.lean', 'Hindman168/BoundedPieceNilFamilies.lean', 'Hindman168/PieceNilHilbertSubspace.lean', 'Hindman168/PieceNilLipschitzComposition.lean', 'Hindman168/FiniteMassHilbertClipping.lean', 'Hindman168/PieceNilHilbertClipping.lean']
COMPONENTS = ['The exact original piecewiseLinearNilsequence is preserved by interval refinement whenever the fine length divides the coarse length. An explicit parent interval/residue map works for ALL integer inputs, keeps the modulus and the global y/M orbit exponent unchanged, and master-parameter ordered gaps supply the divisibility.', 'Actual bounded piecewise orbit representations on a fixed quotient have a single observable bound and Lipschitz constant across all stages and pieces. Refinement preserves these exact constants and the same quotient, translations and basepoints by reindexing.', 'These actual representing families are realized in the ORIGINAL-law ultrafilter Hilbert space. Their actual closed linear spans are proved nested under refinement, have genuine orthogonal projections, and satisfy the exact paper projection-energy identity.', 'Arbitrary Lipschitz real composition of the actual observables preserves representation on the SAME quotient with explicit global bound K*B+abs(psi(0)) and Lipschitz constant K*Lip. In particular unit-interval clipping preserves the representing family.', 'Unit-interval clipping contracts distance to [0,1]-valued targets pointwise, in the ORIGINAL weighted L2 seminorm, and in the actual completed ultrafilter Hilbert space. Clipped genuine representatives remain in the actual closed span; Pythagorean decomposition then proves the actual projected-distance contraction.']
REMAINING = "Original native geometry and original-law ambient ultrafilter Hilbert space remain proved. The exact piecewise orbit definition now has proved interval refinement, uniform-bound/Lipschitz preservation, actual Hilbert realization and closed-span nesting with genuine projection energy identity on each fixed quotient. Lipschitz real composition and unit-interval clipping of genuine representatives are proved, including original weighted L2 and projected-distance contraction. These general fixed-quotient lemmas do NOT yet construct the entire space of all step-at-most-s nilmanifold recipes. Next prove product-quotient representation and finite linear-combination/common-complexity closure, assemble the full admissible nilsequence closed spans, then instantiate clipped dense approximation and Ramsey selection with the paper's padding/principal tuple indexing. Calibration/Alignment, subgroup inverse inputs, actual coloring/arithmetic data and ordered positive rapidly separated monochromatic witnesses, plus quantitative bounds where required, remain. The original models, groups, Gamma, sampling laws and StrongConjecture statement are unchanged. StrongConjecture and the prize target are unproved. No unavoidable blocker is established; publication, PR and prize application remain pending."


def declarations():
    return {p: old.declarations(p) for p in MODULES}


def register():
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 939
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for values in ds.values() for _, name in values]
    assert len(names) == len(set(names)) == 28
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 20
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 939, 'modules': MODULES,
        'names': names, 'theorem_count': 20, 'declarations': ds})
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
    assert len(own) == 927 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for ds in declarations().values() for _, n in ds]
    assert names == registration['names'] and len(names) == 28
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
    assert len(registered) == len(set(registered)) == len(actual) == 4545
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
    assert len(files) == len({f['path'] for f in files}) == 945
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=20, new_definitions=7, new_instances=1, new_axiom_reports=28, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True, full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. Prior audit rechecked before edits. All 939 baseline source/config hashes checked before registration; only root imports and registry change. Original statements, retained proofs, source pins, groups, lattices and sampling laws remain unchanged.', 'The source route is 05_prediction.tex nested-spaces and the clipping argument in energy-selection. The implementation uses the RETAINED actual piecewiseLinearNilsequence, not a newly substituted simplified orbit definition.', 'The explicit parent map is (intervalIndex / (coarseLength/fineLength), residue). The proof uses exact natural divisibility and integer Euclidean division with nonnegative divisor, so it covers negative roots as well. The original orbit is globally anchored at y/M, so reindexing suffices without a fictitious basepoint shift. Ordered master gaps provide actual divisibility.', 'IsBoundedPieceNilsequence retains one B and one Lip valid at every w, every piece and every quotient point. Translations and basepoints may vary freely, as in the retained tests. Refinement copies these constants exactly. The fixed quotient is arbitrary in this general lemma; no nilpotence, compactness or step bound is falsely inferred from the name.', 'Hilbert generators are actual canonical images of L2-bounded original-law families satisfying this representation predicate. Probability laws and the global observable bound prove every representing family has such an image. Closed spans use actual Submodule.span and topologicalClosure. Generator inclusion proves closed-span inclusion; completeness supplies the genuine orthogonal projections.', 'Real Lipschitz composition is built by actual continuous-observable composition with the same g, x and quotient. The global bound is K*B+abs(psi(0)), and the new Lipschitz constant is K*Lip. UnitIntervalClip is explicitly max 0 (min 1 t), is 1-Lipschitz, and fixes every [0,1] target.', 'Clipping contraction is proved in the original coordinate L2 seminorm using nonnegative original weights and the actual support; zero weights are untouched. The ultrafilter comparison of squared-distance limits passes this inequality to the SAME completed Hilbert space. The target need only be [0,1]-valued on the original supports.', 'Clipped genuine representatives are proved to belong to the actual generator set and hence the actual closed span. The retained Pythagorean comparison proves contraction relative to the genuine orthogonal projection. This does not claim that finite linear combinations of arbitrary recipes are already represented: product-quotient closure and finite common complexity are still required.', 'All retained empty-axiom reports are preserved. The new pure integer parent-map definition is expected to have an empty axiom report; its exact name is checked. Every other report remains restricted to the standard foundational axioms. No full-target or publication claim is made; no unavoidable blocker is established.'], new_modules=MODULES, verified=summary, remaining=REMAINING)
    manifest = dict(baseline)
    manifest.update(files=files, hindman_module_count=927, pntplus_module_count=9,
        selected_axiom_report_count=4545, source_scan_module_count=936,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=6, new_theorem_count=20,
            new_selected_report_count=28, retained_proof_sources_changed=False,
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
