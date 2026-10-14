"""Register and audit the common coloring Hilbert/native family and rho-S count replacement."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-principal-calibration-count'
OLD = 'round-selected-relabel-count'
EXPECTED_NEW_AXIOM_FREE = set()
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/PrincipalSubsetProductLaws.lean', 'Hindman168/PrincipalBlockCalibration.lean', 'Hindman168/PrincipalWeightedColorCounts.lean', 'Hindman168/PrincipalPredictionModels.lean']
COMPONENTS = ['The actual finite selected tail product law equals the original tailMass through an explicit equivalence between a finite subset and its principal image. The equality holds without normalization assumptions. Selected subset products also equal the original image-coordinate products exactly.', 'The color coefficient of a selected block is the rational floor of its actual selected subset scale times the requested factor, exactly equal to the original coefficient. Sampling that finite block under the selected independent harmonic mass gives the actual original block-product law for every test and event, eventually. Unused coordinates disappear by their proved actual total mass one.', 'The relabeled weighted count is written with the actual selected pivot product laws, independent tail-product divisor weights, singleton center weights, all nonsingleton weighted color rows and all nonempty product-color masks. Each weight and the full count equal their original lifted expressions, with coefficient positivity supplied eventually by actual master conditions.', 'The identical selected native model family now has block calibration under the selected independent raw harmonic law and complete actual selected weighted-versus-bounded color counting at the prescribed independent tolerances. All prior admissibility, original laws, testing, finite-coordinate count and common-manifold properties are preserved. Native inverse existence remains an explicit unproved input.']
REMAINING = 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional on those inverse inputs, the same selected native models have actual admissible parameters, actual selected block calibration and complete selected weighted-versus-bounded color count at independently prescribed tolerances chosen before N. The relabeled raw harmonic product law, tail-product divisor law, pivot product law, coefficients, normalized forms, singleton center weights and all nonempty product-color masks are now connected by exact proved identities. Full Prediction output integration still needs the precise ultrafilter-limit statements, finite scale-list closure specialization and any remaining model representation details, as well as unconditional inverse inputs. Alignment and final ordered positive rapidly separated monochromatic extraction remain incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'


def declarations():
    ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|instance)\s+([A-Za-z][A-Za-z0-9_\.]*)', old.lean_code(read(p)), re.M) for p in MODULES}
    return ds


def register():
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 1269
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for p, values in ds.items() for _, name in values]
    assert len(names) == len(set(names)) == 21
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 13
    assert sum(kind in {'def', 'abbrev'} for values in ds.values() for kind, _ in values) == 8
    assert not any(kind == 'instance' for values in ds.values() for kind, _ in values)
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 1269, 'modules': MODULES,
        'names': names, 'theorem_count': 13, 'selected_report_count': 21, 'declarations': ds})
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
    assert len(own) == 1255 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for p, ds in declarations().items() for _, n in ds]
    assert names == registration['names'] and len(names) == 21
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
    assert len(registered) == len(set(registered)) == len(actual) == 5631
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert all(actual[n] == v for n, v in previous.items())
    assert all(v <= old.ALLOWED for v in actual.values())
    assert {n for n, v in actual.items() if not v} == EXPECTED_NEW_AXIOM_FREE | old.AXIOM_FREE | {'Hindman168.intervalResidueParent', 'Hindman168.completeResidueCellPoint', 'Hindman168.integerCubeResidueShift', 'Hindman168.admissible_option_selection_none'}
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
    assert len(files) == len({f['path'] for f in files}) == 1273
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=13, new_definitions=8, new_structures=0, new_instances=0, new_axiom_reports=21, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True,
        axiom_free_reports=sorted(n for n, v in actual.items() if not v),
        new_axiom_free_reports=sorted(EXPECTED_NEW_AXIOM_FREE), full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-11', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. The preceding selected relabel count audit was terminal-successfully rechecked and its authoritative manifest copied before new proof edits. All retained proof sources stay unchanged.', 'The subset-image equivalence uses injectivity of the genuine principal order embedding and surjectivity from actual finite-image membership. The full tail-law equality follows by piMass reindexing and equality of finite products, then by the retained raw-product law for the actual increasing enumeration. No normalization or independence input is added to this identity.', 'Subset and one-block sample identities convert dependent subtype products to ordinary finite-set products before image rewriting. This preserves the actual master-coordinate Fin M indices and avoids silently changing dependent enumeration instances. The block tail is nonempty and strictly before its pivot.', 'Block calibration uses exact selected-coordinate expectation transport and the retained actual original block-product event law. The arbitrary event is transported at each sufficiently late stage. The selected block coefficient equals the actual original rational floor, so there is no assumed rounding replacement or changed color argument.', 'The selected divisor weight is built from the actual independent tail-product pushforward, not an abstract equivalent density. The pivot law remains the exact original harmonic integer piMass. The mask-generated master is independent of gap metadata, so the same actual family is used for both chain and original block weights.', 'The weighted count is the expectation of all singleton center divisor factors times the full nonsingleton weighted-color integrand and complete product mask. The original correlation equality uses the retained singleton factor theorem and actual eventual coefficient positivity. No unbounded factor is dropped or bounded-test approximation substituted for an exact identity.', 'The final assembly keeps exactly the e, model and parameter witnesses from selected_color_relabel_models. Its new local block calibration rewrites the retained original product calibration; its new full local weighted comparison rewrites the retained original correlation by the proved weighted count identity. All calibration and counting tolerances remain chosen before N.', 'Four new modules contain thirteen theorems and eight definitions. No new resource options, axioms, sorry, admit or native_decide are allowed. Full build and kernel reports must finish without warnings. Retained proof hashes and full axiom sets must remain unchanged except root imports and registry.', 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional on those inverse inputs, the same selected native models have actual admissible parameters, actual selected block calibration and complete selected weighted-versus-bounded color count at independently prescribed tolerances chosen before N. The relabeled raw harmonic product law, tail-product divisor law, pivot product law, coefficients, normalized forms, singleton center weights and all nonempty product-color masks are now connected by exact proved identities. Full Prediction output integration still needs the precise ultrafilter-limit statements, finite scale-list closure specialization and any remaining model representation details, as well as unconditional inverse inputs. Alignment and final ordered positive rapidly separated monochromatic extraction remain incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'], new_modules=MODULES, verified=summary, remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='02_framework exact weighted count and block calibration; 05_prediction complete selected-law transport')
    manifest = dict(baseline)
    manifest.update(date='2026-10-11', files=files, hindman_module_count=1255, pntplus_module_count=9,
        selected_axiom_report_count=5631, source_scan_module_count=1264,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=4, new_theorem_count=13,
            new_selected_report_count=21, retained_proof_sources_changed=False,
            root_and_registry_changed=True, review_file=PREFIX+'-review.json', remaining=REMAINING))
    manifest['proved_components'] = baseline['proved_components'] + COMPONENTS
    audit = read('AUDIT.txt')
    marker = 'Remaining proof work:'
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline['last_round']['remaining']
    note = '\n2026-10-11 ' + PREFIX + ': PROGRESS. ' + ' '.join(COMPONENTS) + '\n'
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
    assert Path('BUILD-EVIDENCE.txt').read_bytes() == b'=== COMPLETE BUILD OUTPUT ===\n' +\
        Path(PREFIX+'-build.txt').read_bytes()+b'\n=== COMPLETE AXIOM OUTPUT ===\n'+\
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
