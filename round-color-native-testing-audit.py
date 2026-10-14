"""Register and audit the common coloring Hilbert/native family and rho-S count replacement."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-color-native-testing'
OLD = 'round-color-block-hilbert-family'
EXPECTED_NEW_AXIOM_FREE = set()
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/MaskColorFamilyCoarseDualControl.lean', 'Hindman168/NativeMetricMaskModelTesting.lean', 'Hindman168/MaskColorBlockNativeTesting.lean', 'Hindman168/NativeCoarseProjectionTesting.lean', 'Hindman168/MaskColorCoarseNativeTesting.lean', 'Hindman168/SelectedColorBlockCoarseTesting.lean', 'Hindman168/SelectedColorNativeTestingModels.lean']
COMPONENTS = ['Every tracked block transfers the same preselected color dense model to actual original chain dual control at each permissible gap. Only that tracked tail and pivot are required to bracket the gap, so its own selected coarse padding is permitted without imposing the common fine gap on other columns.', 'The prescribed native quotient metric induces exactly the natural quotient topology, proved from the native metric quotient-map property. Actual lower-central cube compactness and natural quotient compactness are transported to that metric topology without changing the distance or Lipschitz constants. Original zero-prime testing now applies uniformly to the actual step-bounded native test recipes.', 'Actual color dense-model dual control proves original harmonic rho-F native testing at every valid block gap. The original native family retains all stages and its prescribed metric; the zero-prime component of the actual template catalogue supplies the tests at dimension s+1. No inverse existence assumption is used for this testing step.', 'Coarse projection approximation controls the original completed Hilbert pairing with every actual native unit-bounded coarse family. Orthogonality identifies the f pairing with its coarse projection, and the original subprobability law proves the test norm bound at every stage. The original expectation ultralimit then gives the eventual f-S test estimate.', 'The actual rho-F limit and f-S coarse approximation combine to an eventual original rho-S test bound below the projection accuracy plus any positive slack. The same f, S, native test, master coefficient and original pivot mass are retained throughout; no inverse hypothesis or assumption of rho-F testing is inserted.', 'For the actual selected principal indices, a valid nonempty tail preceding its pivot also precedes its own coarse padding. The exact masterGapIndex at that padding constructs the permissible block gap. A raw globally unit-bounded native test is realized in the same original Hilbert law without altering any stage.', 'The same selected coloring native model family now simultaneously retains coarse native representation, projection accuracy, global unit bounds, all original rho-S subset-count replacements and one common native manifold, and additionally satisfies original rho-S coarse native testing at each valid selected block. The inverse existence inputs remain explicit and unproved. Each test family is fixed before its eventual stage; no uniform stage over all native families is claimed.']
REMAINING = 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. The finite-list native periodic interval inverse existence statement remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. The same actual coloring dense Hilbert family now supports selected native models, the complete original rho-S subset-count replacement and own-coarse-gap native testing, conditional on those inverse inputs for the selected model existence. The coarse testing transfer itself has no inverse hypothesis. The full coloring Prediction Principle still requires its calibration against actual product sampling, parameter and output integration. Calibration/Alignment and the final ordered positive rapidly separated monochromatic extraction remain incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'


def declarations():
    return {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|instance)\s+([A-Za-z][A-Za-z0-9_\.]*)', old.lean_code(read(p)), re.M) for p in MODULES}


def register():
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 1228
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for p, values in ds.items() for _, name in values]
    assert len(names) == len(set(names)) == 13
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 13
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 1228, 'modules': MODULES,
        'names': names, 'theorem_count': 13, 'selected_report_count': 13, 'declarations': ds})
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
    assert len(own) == 1217 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for p, ds in declarations().items() for _, n in ds]
    assert names == registration['names'] and len(names) == 13
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
    assert len(registered) == len(set(registered)) == len(actual) == 5514
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
    assert len(files) == len({f['path'] for f in files}) == 1235
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=13, new_definitions=0, new_instances=0, new_axiom_reports=13, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True, full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-11', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. The preceding coloring Hilbert-family audit was terminal-successfully rechecked and its unchanged authoritative manifest copied before these proof edits. The immediately preceding goal turn proved the last native block testing lemma after resolving definitional identifications, and verified official rules continue to accept complete Lean contributions. No completed prize proof or eligibility is claimed.', 'The actual tracked-block template control is transferred at the same tail and pivot. Its gap need only follow this tail and precede this pivot. This correctly permits each block own coarse padding, rather than imposing the fine gap conditions simultaneously on unrelated columns.', 'Natural quotient topology and the topology of the prescribed native metric are proved equal from the actual metric quotient-map property. Explicit equality transport carries the original compact quotient and the proved lower-central corner cube compactness to that topology. This avoids silently choosing another metric or assuming unproved layer compactness.', 'The zero-prime member of the original dual catalogue has arity zero and dimension s+1. The native step bound is s, so its lower-central filtration is terminal at s+1. Each actual stage-varying native recipe is supplied as an admissible test to the proved uniform original-law testing theorem. The original weight and actual pivot law are preserved.', 'The coarse Hilbert test is proved by projection orthogonality and Cauchy-Schwarz. Every original pivot law is a subprobability law at all stages, including possible zero initial laws, so the globally unit-bounded test has completed norm at most one without changing early stages. The exact completion linear map identifies f-S, and the original pairing convergence yields an eventual expectation bound.', 'The rho-S identity is the exact sum of rho-F and F-S pairings. The actual rho-F theorem supplies vanishing error, and the same model coarse projection supplies the second bound. Half-slack bounds and the real triangle inequality prove the result for any positive slack without a new inverse assumption.', 'Actual selected tail positions image lies in the selected principal set. The retained energyTail_before_padding theorem gives all tail indices before the selected own padding, while padding is before the pivot. The proved masterGapIndex value is used on its actual master range; its stage-constant definition preserves the given coarse native representation and projection approximation.', 'The assembly selects exactly the f and S witnesses from the retained coloring selected model theorem, preserving all earlier count replacements, unit bounds and common native geometry. The additional raw native testing property refers to those exact S witnesses. Each v and slack are quantified before the eventual stage. It does not assert a single stage uniform over arbitrary bounded-complexity classes, nor erase the explicit interval inverse existence premise.', 'All thirteen new theorems are selected for transitive kernel audit. Focused compilation, complete build, kernel audit and authoritative recheck must all finish successfully without warnings. No new definitions, instances, resource options, proof axioms or forbidden proof steps are introduced.', 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. The finite-list native periodic interval inverse existence statement remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. The same actual coloring dense Hilbert family now supports selected native models, the complete original rho-S subset-count replacement and own-coarse-gap native testing, conditional on those inverse inputs for the selected model existence. The coarse testing transfer itself has no inverse hypothesis. The full coloring Prediction Principle still requires its calibration against actual product sampling, parameter and output integration. Calibration/Alignment and the final ordered positive rapidly separated monochromatic extraction remain incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'], new_modules=MODULES, verified=summary, remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='05_prediction: original rho-S coarse native testing on the same selected models')
    manifest = dict(baseline)
    manifest.update(date='2026-10-11', files=files, hindman_module_count=1217, pntplus_module_count=9,
        selected_axiom_report_count=5514, source_scan_module_count=1226,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=7, new_theorem_count=13,
            new_selected_report_count=13, retained_proof_sources_changed=False,
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
