"""Register and audit the common coloring Hilbert/native family and rho-S count replacement."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-bounded-count-sampling'
OLD = 'round-calibration-tolerance-cap'
EXPECTED_NEW_AXIOM_FREE = set()
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/FiniteProductDensityLaw.lean', 'Hindman168/OriginalChainWeightedSampling.lean', 'Hindman168/SubsetSingletonFactors.lean', 'Hindman168/MaskBoundedCountSampling.lean', 'Hindman168/SelectedColorRawCounting.lean', 'Hindman168/SelectedColorPredictionTolerance.lean', 'Hindman168/MaskColorProductMasks.lean', 'Hindman168/SelectedColorProductCounting.lean']
COMPONENTS = ['Finite signed product comparison masses are exactly their original pivot product mass times the product of their actual divisor densities. The proved expectation identity keeps all coefficients and does not renormalize the comparison mass.', 'For actual valid master chains, the full raw-coordinate product statistics approximate the original weighted pivot product law uniformly over every joint real test bounded by one. This follows from the retained actual list-valued joint L1 comparison by the injectivity of List.ofFn and exact coordinatewise integer pushforward.', 'Every small nonempty subset is its singleton maximum. With actual positive natural coefficients its normalized integer sum form is exactly that coordinate. The product of all singleton rows is therefore precisely the original product of center divisor weights, with no singleton color mask removed.', 'The original model subset correlation is exactly the weighted original pivot expectation of the bounded nonsingleton model integrand and complete product mask. Its bound one is proved from the actual model unit bounds and all nonempty-subset mask unit bounds. Uniform joint sampling transport applies to the full integrand, even for stage-varying masks and model inputs.', 'The same selected native model family now satisfies original unbounded color-count versus complete original raw-coordinate bounded-model-count comparison, while retaining both calibrated laws, native testing, all original subset correlations and one common native manifold. The earlier replacement estimate is applied to the actual center-and-color row family after proving its admissibility from actual divisor and color-weight bounds.', 'The count replacement accuracy is countTolerance divided by twice the number of nonsingleton terms plus two. It is positive and its total replacement budget equals countTolerance/2. Choosing this accuracy before N and using sampling slack countTolerance/2 yields a strict eventual counting error below the prescribed countTolerance on the same calibrated models.', 'The actual product-color mask evaluates the color of the product of all original natural master coefficients times the product argument for each nonempty column subset. It includes singleton subsets. On positive natural coordinate products it is exactly the indicator of the product of the scaled coordinates having the chosen color. The same selected family has the prescribed raw count comparison with these concrete masks.']
REMAINING = 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional on those inverse inputs, the same actual selected coloring model family now supports calibration under original block-product and complete raw-coordinate laws and full raw-coordinate bounded count comparison at prescribed independent tolerances, including the concrete complete product-color masks. Both approximation tolerances are chosen before the master index count N. The former missing final bounded joint sampling count replacement is resolved in the new route. The full Prediction Principle still needs unconditional inverse inputs and admissible parameter, selected-index relabeling, exact paper scale/form and ultrafilter-limit output integration. Alignment and final ordered positive rapidly separated monochromatic extraction remain incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'


def declarations():
    ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|instance)\s+([A-Za-z][A-Za-z0-9_\.]*)', old.lean_code(read(p)), re.M) for p in MODULES}
    ds[MODULES[0]] = [(kind, 'FiniteMass.' + name) for kind, name in ds[MODULES[0]]]
    return ds


def register():
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 1251
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for p, values in ds.items() for _, name in values]
    assert len(names) == len(set(names)) == 25
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 21
    assert sum(kind in {'def', 'abbrev'} for values in ds.values() for kind, _ in values) == 4
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 1251, 'modules': MODULES,
        'names': names, 'theorem_count': 21, 'selected_report_count': 25, 'declarations': ds})
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
    assert len(own) == 1241 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for p, ds in declarations().items() for _, n in ds]
    assert names == registration['names'] and len(names) == 25
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
    assert len(registered) == len(set(registered)) == len(actual) == 5565
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
    assert len(files) == len({f['path'] for f in files}) == 1259
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=21, new_definitions=4, new_instances=0, new_axiom_reports=25, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True,
        axiom_free_reports=sorted(n for n, v in actual.items() if not v),
        new_axiom_free_reports=sorted(EXPECTED_NEW_AXIOM_FREE), full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-11', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. The preceding capped calibration audit was terminal-successfully rechecked and its authoritative manifest copied before new proof edits. All retained proof sources must stay unchanged.', 'The finite product density identity proves support inclusion from the actual pointwise mass identity, expands both expectations over the original support and retains all factors. It permits signed masses and arbitrary tests; no normalization assumption is used.', 'The actual natural coordinate L1 error equals the retained actual list-valued error because List.ofFn is injective. Taking the constant sampling budget one in the proved master rapid estimate yields convergence to zero. The unit test bound is genuinely uniform at the stage; model and product mask inputs can vary with w.', 'Coordinatewise casting to integers is the proved piMass_map pushforward. The integer comparison component is exactly the original harmonic pivot mass times its integer divisor mask on all integers, including negative arguments. No abstract law equality or extra error assumption replaces the actual construction.', 'The singleton product is identified by an explicit equivalence from small nonempty subsets to their maximum coordinate. The positive coefficient condition is essential to the c/c=1 identity and is derived eventually from actual MasterParameterConditions.column_coefficients with the finite image of the positive scale family.', 'The original subset product is split into its exact singleton divisor product and nonsingleton model product. All nonempty product-mask factors, including singleton masks, remain. The full model integrand is proved bounded by one, so the actual joint sampling theorem applies even though the retained center weights are unbounded.', 'The concrete center-and-color family is proved admissible from actual nonnegative divisor masks and color weights bounded by the corresponding original divisor mask. The previously proved rho-S replacement theorem is called on that specific family and on the same selected S witnesses, then the proved bounded count sampling theorem is applied.', 'The count accuracy countTolerance/(2*(L+1)) is chosen before N and proved positive; field algebra proves (L+1)*accuracy=countTolerance/2. The remaining sampling slack is the other half. Calibration cap and count tolerance are prescribed independently before N, while the final stage may depend on the fixed count and event parameters.', 'The complete product-color mask uses all nonempty subsets and the original natural coefficients. The positive-natural-coordinate identity uses exact finite product multiplication, not an assumed replacement of rational scaling. General selected counting is specialized to these concrete masks using their proved unit bounds.', 'Eight new modules contain twenty-one theorems and four definitions. No new resource options, axioms, sorry, admit or native_decide are allowed. Full build and registered transitive kernel reports must finish successfully without warnings. All retained proof hashes and axiom sets must remain unchanged, except root imports and the axiom registry.', 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional on those inverse inputs, the same actual selected coloring model family now supports calibration under original block-product and complete raw-coordinate laws and full raw-coordinate bounded count comparison at prescribed independent tolerances, including the concrete complete product-color masks. Both approximation tolerances are chosen before the master index count N. The former missing final bounded joint sampling count replacement is resolved in the new route. The full Prediction Principle still needs unconditional inverse inputs and admissible parameter, selected-index relabeling, exact paper scale/form and ultrafilter-limit output integration. Alignment and final ordered positive rapidly separated monochromatic extraction remain incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'], new_modules=MODULES, verified=summary, remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='05_prediction: complete bounded count sampling and prescribed tolerance on the same calibrated selected family')
    manifest = dict(baseline)
    manifest.update(date='2026-10-11', files=files, hindman_module_count=1241, pntplus_module_count=9,
        selected_axiom_report_count=5565, source_scan_module_count=1250,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=8, new_theorem_count=21,
            new_selected_report_count=25, retained_proof_sources_changed=False,
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
