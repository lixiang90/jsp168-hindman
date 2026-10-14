"""Register and audit the common coloring Hilbert/native family and rho-S count replacement."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-color-block-hilbert-family'
OLD = 'round-mask-block-all-gap-models'
EXPECTED_NEW_AXIOM_FREE = set()
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/MaskColorBlockHilbertFamily.lean', 'Hindman168/MaskColorFamilyChainReplacement.lean', 'Hindman168/MaskColorFamilySelectedQuality.lean', 'Hindman168/MaskUnitNativeReplacement.lean', 'Hindman168/MaskColorNativePredictionTransfer.lean', 'Hindman168/SelectedColorDenseNativeModels.lean']
COMPONENTS = ['The actual all-gap coloring dense models now form one global unit-bounded family in the original pivot Hilbert spaces, constructed before the ultrafilter, energy indices and chains. Invalid block coordinates have a zero representative; every valid block retains all actual mask and zero-prime dual tests at all permissible gaps and positive quotient scales.', 'That same family simultaneously replaces every nonsingleton color-weight factor in every later valid chain. Exact block-mask identification transfers the actual color bounds and actual template pairing proves rho-F cube convergence. The proved original finite telescoping bound controls replacement against arbitrary admissible companion factors and product masks.', 'Actual selected principal coordinates give the block-range, common fine-gap and tail hypotheses for the same family. Its rho-F replacement quality holds at the actual first selected padding and transfers to any tail-containing ultrafilter with no new choice of dense models.', 'An exact finite native replacement path turns F-S error correlations into a total bounded-model replacement error of L times the tested error, where L is the actual number of nonsingleton mask supports. Double subset replacement is exactly idempotent for the final models.', 'The rho-F replacement and F-S estimates now combine on their actual constructed admissible error families along the same ultrafilter. No unproved uniform-stage estimate is inferred from a bound for arbitrary input sequences. The complete original rho-S subset replacement error is at most (L+1) times the tested accuracy.', 'Given the still explicit finite list of interval inverse existence inputs, one actual coloring dense family chosen before all ultrafilters now supplies the same selected native coarse model family. All selected chains have both the actual rho-F replacement, the actual F-S target estimates and their proved total original rho-S subset-count replacement. The same native models retain their own coarse representations, projection accuracy, global unit bounds and common native manifold with uniform observable bounds. Analytic thresholds and required master count precede the coloring and coefficients.']
REMAINING = 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. The finite-list native periodic interval inverse existence statement remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. The same actual coloring dense Hilbert family now supports selected native models and the complete original rho-S subset-count replacement, conditional on those inverse inputs. This does not prove the entire coloring Prediction Principle: its remaining native/coarse testing, parameter and output integration must be completed. Calibration/Alignment and the final ordered positive rapidly separated monochromatic extraction remain incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'


def declarations():
    return {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|instance)\s+([A-Za-z][A-Za-z0-9_\.]*)', old.lean_code(read(p)), re.M) for p in MODULES}


def register():
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 1222
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for p, values in ds.items() for _, name in values]
    assert len(names) == len(set(names)) == 12
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 10
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 1222, 'modules': MODULES,
        'names': names, 'theorem_count': 10, 'selected_report_count': 12, 'declarations': ds})
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
    assert len(own) == 1210 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for p, ds in declarations().items() for _, n in ds]
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
    assert len(registered) == len(set(registered)) == len(actual) == 5501
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
    assert len(files) == len({f['path'] for f in files}) == 1228
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=10, new_definitions=2, new_instances=0, new_axiom_reports=12, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True, full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-11', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. The preceding all-gap color dense-model round was terminal-successfully rechecked and its unchanged authoritative manifest copied before proof edits. The present proof family preserves all earlier sources, selected axioms and pinned mathematical references.', 'Every valid tail/pivot/color/coefficient block receives the actual model constructed by the prior all-gap theorem. Invalid coordinates are zero, so the energy input family is total and globally unit bounded. The original harmonic laws are subprobability laws at every initial stage; the retained original bounded-family constructor therefore supplies actual Hilbert membership without modifying initial stages.', 'Actual chain color weights use the same original master coefficient and the same tail as the one-column block realization. The actual block divisor mask depends only on that tail. Selecting a later chain thus does not select another dense model. All nonsingleton replacements use the same original correlation, integer forms and product masks.', 'The common fine padding is the first selected padding. The proved principal-coordinate recovery gives its order before every pivot and after every tail. The total masterGapIndex agrees with the actual padding on its proved master range, at every w.', 'The bounded F-S path visits every actual nonsingleton mask support exactly once. Its error factor is bounded by one since both model values are in [0,1]; eventual nonnegativity of the original divisor mask gives the original admissibility bound. The exact update difference and finite real triangle inequality give L times the single-target accuracy. Singleton and product factors retain their original place in the actual count.', 'The retained selected native theorem bounds every admissible input sequence; it does not state an arbitrary uniform-stage bound. The new transfer supplies only the finitely many actual intermediate error sequences needed for this input count and uses their proved eventual admissibility. Finite eventual intersection then suffices for the actual telescoping bound. This avoids an invalid quantifier exchange and needs no assumption of target cube smallness.', 'The coloring dense family is chosen before the ultrafilter and selected indices. The same family is passed to the proved selected native model theorem, with all coarse representation, approximation, unit-bound and common native observable properties retained. The constructed rho-F and F-S estimates supply the full original rho-S subset-count replacement. The finite list of interval inverse existence hypotheses remains explicit throughout.', 'All twelve new declarations are selected for transitive kernel audit. Focused compilation, complete build, kernel audit and authoritative recheck must all be warning-free and terminal successful. No new resource options or forbidden proof steps are permitted.', 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. The finite-list native periodic interval inverse existence statement remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. The same actual coloring dense Hilbert family now supports selected native models and the complete original rho-S subset-count replacement, conditional on those inverse inputs. This does not prove the entire coloring Prediction Principle: its remaining native/coarse testing, parameter and output integration must be completed. Calibration/Alignment and the final ordered positive rapidly separated monochromatic extraction remain incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'], new_modules=MODULES, verified=summary, remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='05_prediction: one coloring Hilbert family and actual selected native rho-S count replacement')
    manifest = dict(baseline)
    manifest.update(files=files, hindman_module_count=1210, pntplus_module_count=9,
        selected_axiom_report_count=5501, source_scan_module_count=1219,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=6, new_theorem_count=10,
            new_selected_report_count=12, retained_proof_sources_changed=False,
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
