"""Register and audit the rational-functional increment against its saved baseline."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-rational-subgroup-character'
OLD = 'round-rational-functional'
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/RationalRestrictedKernel.lean', 'Hindman168/NativeRationalSubgroupCharacter.lean', 'Hindman168/NativeRationalCharacterKernel.lean', 'Hindman168/NativeCharacterLatticeReduction.lean', 'Hindman168/NativeRationalCompactRepresentatives.lean', 'Hindman168/NativeRationalLatticeCompact.lean']
COMPONENTS = ['Real kernels restricted to arbitrary rational subspaces are spanned by their original rational vectors, by explicit rank-one rational pivot projection; nonzero restriction strictly lowers dimension.', 'Every nonzero original Gamma-rational Lie subalgebra has a real character annihilating its INTERNAL bracket and rational on the SAME full lattice rational form. The character is not required to annihilate the ambient derived algebra.', 'The original BCH finite polynomial layer theorem proves character additivity within the original exponential subgroup. Its actual kernel is the exponential of a smaller Gamma-rational native Lie subalgebra, with an actual original Gamma intersection pivot.', 'Actual original pivot reduction writes g = Exp(r Log gamma) u gamma^z with 0<=r<=1, u in the smaller original kernel and gamma^z in the SAME specified Gamma, without lattice normality or discrete character-image hypotheses.', 'A complete strong induction on real dimension constructs compact left representatives for EVERY Gamma-rational original native Lie subgroup and its SAME Gamma intersection; no supplied subgroup cocompactness remains.', 'The actual restricted-lattice natural quotient is compact and metrizable, its natural inclusion into the original ambient quotient is a closed embedding, and the original orbit is compact. Intersection discreteness is proved by an actual embedding into the specified discrete Gamma.']
REMAINING = "The general original specified-lattice rational subgroup cocompactness requirement is NOW PROVED: for every Gamma-rational native real Lie subalgebra S, its actual Exp(S) subgroup has constructed compact representatives modulo the SAME Gamma, compact metrizable natural restricted-lattice quotient, a closed embedding into G/Gamma and a compact orbit. The full original model, group and Gamma remain unchanged. Next connect this theorem to the paper's actual lower-central layers: prove real lower-central rationality for the now-identified W_Gamma and finish equality of algebraic GROUP lower-central layers with exponentials of the actual real Lie layers, not merely their Q logarithmic spans or closures. Instantiate the existing canonical cube/layer quotient and original-law testing interfaces with these proved compact quotients. Remaining full-target work includes quantitative degree/denominator bounds where required, complete nested coarse-model projections, Calibration/Alignment, actual coloring/arithmetic data and ordered positive rapidly separated monochromatic witnesses. StrongConjecture and the prize target remain unproved. No universal faithful matrix integration theorem is claimed or required by this native compactness proof. No unavoidable blocker is established; publication, PR and prize application remain pending."


def declarations():
    return {p: old.declarations(p) for p in MODULES}


def register():
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 917
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for values in ds.values() for _, name in values]
    assert len(names) == len(set(names)) == 22
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 917, 'modules': MODULES,
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
    assert len(own) == 905 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for ds in declarations().values() for _, n in ds]
    assert names == registration['names'] and len(names) == 22
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
    assert len(registered) == len(set(registered)) == len(actual) == 4435
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
    assert len(files) == len({f['path'] for f in files}) == 923
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=20, new_definitions=2, new_axiom_reports=22, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True, full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. The previous complete audit was freshly rechecked before edits. All 917 retained baseline source/config hashes were checked again before registration; only root and registry are changed. All previous proof sources, StrongStatement, original models/groups/lattices, pins and attributed files are preserved.', 'RationalRestrictedKernel constructs a genuine rank-one projection along an actual rational vector with nonzero functional value. Its images of rational generators lie in the same rational kernel; real span functoriality proves the full restricted kernel equality. The zero restriction is separately handled. The argument assumes rational values, not a discrete image or topological closure of a Q subspace.', 'The character construction uses V=(S restrict_Q) intersect W_Gamma and its INTERNAL rational Lie algebra. Actual inclusion into the nilpotent original algebra proves its lower-central termination. Nilpotent abelianization supplies an element outside its internal derived layer. Rational separation inside the proved full original W_Gamma, followed by the genuine natural scalar extension, constructs F on the original E. Two real span inductions kill brackets only inside S. This covers arbitrary nonzero rational S, not just the ambient group.', 'Rationality and strict dimension descent hold for S intersect ker F. The actual Lie subalgebra T is constructed, and the genuine original global logarithm proves Exp(T) equals the kernel of F Log inside the same original Exp(S). No assumption that S or the lattice is normal in the ambient group is introduced.', 'Actual BCH additivity is obtained by applying the retained rational polynomial layer theorem to the Q scalar restrictions of the REAL spaces S and S intersect ker F. This theorem has no finite-Q-dimension hypothesis and handles ALL real inputs in S. Thus this use does not restrict to rational exponential elements or invoke density without continuity.', 'The retained actual intersection-spanning theorem gives a SAME Gamma intersect Exp(S) pivot gamma with nonzero character. With t=chi(g)/chi(gamma), z=floor t and r=t-z, the genuine residual Exp(-r Log gamma) g gamma^(-z) lies in Exp(T). Actual integer exponential powers, group cancellation and original character additivity establish g=Exp(r Log gamma) u gamma^z, with r in [0,1]. No lattice normality or discrete character image is used.', 'The compact representative theorem is a FULL strong induction on dim_R S. The zero subalgebra has representative {1}. At each nonzero stage the strictly smaller rational T receives the induction hypothesis; its actual compact representatives are multiplied on the LEFT by the compact one-parameter pivot segment. The two RIGHT lattice factors multiply in the SAME Gamma. This completes the original-S induction and proves arbitrary specified-lattice rational subgroup cocompactness.', 'The natural subtype preimage of the compact set is compact, and any remaining Gamma factor belongs to Exp(S) because x and g do. Therefore the quotient uses exactly Gamma.comap Exp(S).subtype. Existing natural quotient inclusion proves a closed embedding; the orbit is compact. Intersection discreteness follows by an embedding into original Gamma. Metrizability follows from the actual exponential homeomorphism with the finite real subspace and compact discrete coset theory.', 'No whole algebraic group/Lie lower-central equality, quantitative bounds, final Calibration/Alignment, positive arithmetic extraction or StrongConjecture is inferred from this result. Publication and submission remain pending. No unavoidable blocker.'], new_modules=MODULES, verified=summary, remaining=REMAINING)
    manifest = dict(baseline)
    manifest.update(files=files, hindman_module_count=905, pntplus_module_count=9,
        selected_axiom_report_count=4435, source_scan_module_count=914,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=6, new_theorem_count=20,
            new_selected_report_count=22, retained_proof_sources_changed=False,
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
