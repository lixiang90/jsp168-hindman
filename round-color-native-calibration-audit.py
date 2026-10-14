"""Register and audit the common coloring Hilbert/native family and rho-S count replacement."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-color-native-calibration'
OLD = 'round-color-native-testing'
EXPECTED_NEW_AXIOM_FREE = set()
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/NativeCalibrationCutoff.lean', 'Hindman168/FiniteCutoffCalibration.lean', 'Hindman168/MaskColorCoarseCalibration.lean', 'Hindman168/OriginalBlockProductTesting.lean', 'Hindman168/MaskColorProductCalibration.lean', 'Hindman168/SelectedColorBlockProductCalibration.lean', 'Hindman168/SelectedColorCalibratedModels.lean']
COMPONENTS = ['The paper calibration cutoff is explicitly 1 minus the unit clipping of (x-2*tau)/tau. It lies in [0,1], equals one below 2*tau and zero above 3*tau, has a proved finite Lipschitz bound for positive tau, and satisfies x*cutoff(x) <= 3*tau for nonnegative x. Composition preserves the same actual native quotient, prescribed metric and orbit.', 'A proved finite weighted calibration inequality bounds the small-model color event by the cutoff error plus 3*tau. The original mass need only be a nonnegative subprobability law, and the color weight may be unbounded. No normalization by a color event mass is used.', 'Actual original rho-S coarse testing applies to the cutoff of the same chosen native model. The original harmonic color event is eventually below 3*tau plus its actual coarse projection accuracy and arbitrary positive slack. This transfer has no inverse existence hypothesis.', 'The actual integer block product law is defined using the original harmonic tail product and original pivot sample. Its divisor comparison expectation is exactly the original pivot expectation with the actual master block mask. The existing proved sampling growth and product-law error estimates give distance convergence to zero and an eventual bound uniform over all globally unit-bounded scalar tests.', 'The actual block-product color-and-small-model event now satisfies calibration below 3*tau plus coarse projection accuracy and arbitrary positive slack. Its indicator uses the same original natural color coefficient and its expectation under the comparison law equals the original weighted color event exactly. The sampling error is derived from the original product law, not inserted as a premise.', 'At selected principal coordinates, every valid nonempty tail precedes the same selected own coarse padding. The exact masterGapIndex agrees with that padding and preserves native representation and approximation. The block-product calibration theorem therefore applies to each exact chosen model.', 'One selected model family now simultaneously retains native coarse representation, projection accuracy, global unit bounds, original rho-S native testing, original rho-S subset-count replacement, a common native manifold and the actual block-product calibration property. The inverse existence hypothesis remains explicit and unproved. The calibration threshold and coarse approximation accuracy are kept separate.']
REMAINING = 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. The finite-list native periodic interval inverse existence statement remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. The same actual selected coloring model family now supports original rho-S subset-count replacement, own-coarse-gap native testing and actual block-product calibration, conditional on the inverse inputs for selected model existence. The testing and calibration transfers themselves have no inverse hypothesis. The full Prediction Principle still needs a coarse approximation tolerance cap chosen before the master count N: the retained selection currently chooses approximation accuracy kappa/4, which is not proved smaller than a separately requested calibration tolerance. Its calibration bound therefore explicitly retains that approximation error. Original global raw-coordinate transport, final bounded count distribution replacement, admissible parameter and output integration also remain. Alignment and final ordered positive rapidly separated monochromatic extraction remain incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'


def declarations():
    return {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|instance)\s+([A-Za-z][A-Za-z0-9_\.]*)', old.lean_code(read(p)), re.M) for p in MODULES}


def register():
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 1235
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for p, values in ds.items() for _, name in values]
    assert len(names) == len(set(names)) == 16
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 14
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 1235, 'modules': MODULES,
        'names': names, 'theorem_count': 14, 'selected_report_count': 16, 'declarations': ds})
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
    assert len(own) == 1224 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for p, ds in declarations().items() for _, n in ds]
    assert names == registration['names'] and len(names) == 16
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
    assert len(registered) == len(set(registered)) == len(actual) == 5530
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
    assert len(files) == len({f['path'] for f in files}) == 1242
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=14, new_definitions=2, new_instances=0, new_axiom_reports=16, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True, full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-11', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. The preceding original coarse native testing audit was terminal-successfully rechecked and its unchanged authoritative manifest copied before these proof edits. All retained proof sources, selected transitive axiom sets and pinned mathematical references must remain unchanged.', 'The actual cutoff matches the paper transition interval [2*tau,3*tau]. Its proved Lipschitz constant is inverse tau, so positive tau is an explicit hypothesis. Observable composition uses the retained boundedPieceNilsequence_lipschitz_comp theorem on the same native data, metric, group and lattice. No replacement quotient or unsupported compactness assumption is introduced.', 'The finite weighted inequality retains every original measure coefficient. Low model values make the cutoff exactly one; elsewhere nonnegativity bounds the event by the weighted cutoff pairing. The model-cutoff product is at most 3*tau and the original subprobability mass is at most one. Only the error pairing and the real triangle/order bounds supply the accuracy loss.', 'The actual color weight is eventually nonnegative by the proved original mask theorem. The model is globally nonnegative and has its original native coarse representation. Its cutoff is globally unit bounded and defines an original bounded Hilbert family without changing initial stages. The proved original rho-S test estimate supplies calibration error, rather than assuming a calibration claim.', 'The comparison measure support lies in the original pivot support because its pointwise density is the actual integer divisor mask. Expanding its expectation over that pivot support identifies exactly the original weighted expectation. The original product-distance convergence follows from actual master-chain sampling growth and the retained integer block product law. Its scalar testing bound is genuinely uniform over all unit-bounded functions at a stage.', 'The original product event indicator is exactly positive integer input, the original natural master color coefficient and the small-model condition. This indicator is bounded by one and its weighted pivot expectation agrees with the original color-weight small-model event by pointwise case analysis. Half-slack for product testing and half-slack for coarse testing give the stated calibration bound.', 'A decidability-instance mismatch between the event indicator and the local test is resolved by proving pointwise equality of their actual values, not by replacing either event. The original weighted law, model and color coefficient are unchanged.', 'The selected calibration assembly preserves exactly the retained chosen f and S witnesses, all count replacements, native test estimates, unit bounds and common native geometry. Every test threshold is fixed before its eventual stage. The positive scalar cutoff threshold is separate from coarse approximation accuracy; no quantifier exchange or uniform stage over all thresholds is claimed.', 'Proof review located a remaining tolerance issue in the retained finite_order_native_shortCube_models: its coarse approximation is kappa/4. That choice is sufficient for the inverse projection test but is not proved below a separately requested calibration tolerance. The current conclusion therefore states 3*threshold + approximation_error + slack. A future proof must choose a capped positive approximation accuracy, such as a minimum with a fraction of the requested tolerance, before selecting N, and carry it through the same energy model construction.', 'All fourteen new theorems and both new definitions are selected for transitive kernel audit. Focused compilation, complete build, kernel audit and authoritative recheck must all finish successfully without warnings. No new instances, resource options, proof axioms or forbidden proof steps are permitted.', 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. The finite-list native periodic interval inverse existence statement remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. The same actual selected coloring model family now supports original rho-S subset-count replacement, own-coarse-gap native testing and actual block-product calibration, conditional on the inverse inputs for selected model existence. The testing and calibration transfers themselves have no inverse hypothesis. The full Prediction Principle still needs a coarse approximation tolerance cap chosen before the master count N: the retained selection currently chooses approximation accuracy kappa/4, which is not proved smaller than a separately requested calibration tolerance. Its calibration bound therefore explicitly retains that approximation error. Original global raw-coordinate transport, final bounded count distribution replacement, admissible parameter and output integration also remain. Alignment and final ordered positive rapidly separated monochromatic extraction remain incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'], new_modules=MODULES, verified=summary, remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='05_prediction: cutoff and original block-product calibration on the same selected models')
    manifest = dict(baseline)
    manifest.update(date='2026-10-11', files=files, hindman_module_count=1224, pntplus_module_count=9,
        selected_axiom_report_count=5530, source_scan_module_count=1233,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=7, new_theorem_count=14,
            new_selected_report_count=16, retained_proof_sources_changed=False,
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
