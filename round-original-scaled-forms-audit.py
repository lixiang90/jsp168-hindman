"""Register and audit the common coloring Hilbert/native family and rho-S count replacement."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-original-scaled-forms'
OLD = 'round-bounded-count-sampling'
EXPECTED_NEW_AXIOM_FREE = set()
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/MaskSubsetScaledForms.lean', 'Hindman168/SelectedPrincipalRawLaw.lean', 'Hindman168/SelectedPrincipalScales.lean', 'Hindman168/SelectedPrincipalGrowth.lean', 'Hindman168/SelectedAdmissibleParameters.lean', 'Hindman168/SelectedColorAdmissibleModels.lean']
COMPONENTS = ['The actual natural-division normalized subset sum form is proved equal to the rational form in the paper once the actual anchor divides every active coefficient. Multiplication by the anchor exactly recovers the scaled integer or natural subset sum. Positive anchor coordinates imply positive forms. Actual master column coefficients supply the positivity, divisibility and exact rational scale ratios eventually, uniformly over all subsets and integer arguments.', 'Restriction of the full original harmonic raw product law to the selected principal indices is exactly the independent product of the original raw laws at those indices. The selected index map is injective; all discarded coordinates have actual total mass one. Exact expectation transport holds for arbitrary joint real tests, and actual selected mass nonnegativity and normalization are proved eventually.', 'Selected subset scales are literally products of the selected original singleton master scales and equal the original master scale of their image. Positivity, powers of W, divisibility by and bounds under the actual common modulus, and the adding-block W^w divisibility all hold on these selected scales. The adding-block relation is transported by the strict principal-index embedding.', 'The actual own padding gap dominates every fixed power of the selected earlier-cutoff auxiliary, with squared cutoffs giving a stronger bound than the paper needs. The log of the actual selected principal cutoff dominates powers of its own padding gap. This uses the proved original gap growth, actual subset product bound and original earlier-gap divisibility; no new asymptotic assumption is inserted.', 'The same selected principal indices and the same native model witnesses now carry the proved SelectedAdmissibleFamily package, including smooth modulus powers, selected scale bounds, adding relations, own gap and cutoff growth, dyadic cutoffs and actual harmonic product probability. All retained model quality, calibration, testing, complete product-color counting and common-manifold properties are preserved. Native inverse existence is still an explicit unproved input.']
REMAINING = 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional on those inverse inputs, the same selected native coloring models support both actual calibrated laws and bounded raw-coordinate count comparison at independent prescribed tolerances chosen before N. The actual selected original scales, own padding gaps, dyadic principal cutoffs and independent harmonic raw laws now satisfy the selected admissible family conditions. The original integer subset forms are proved to match the paper rational forms and to recover the actual scaled natural sums. Full Prediction output integration still needs selected-index relabeling of the complete block and count expressions and the precise ultrafilter-limit statements, as well as unconditional inverse inputs. Alignment and final ordered positive rapidly separated monochromatic extraction remain incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'


def declarations():
    ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|instance)\s+([A-Za-z][A-Za-z0-9_\.]*)', old.lean_code(read(p)), re.M) for p in MODULES}
    return ds


def register():
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 1259
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for p, values in ds.items() for _, name in values]
    assert len(names) == len(set(names)) == 26
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 22
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 1259, 'modules': MODULES,
        'names': names, 'theorem_count': 22, 'selected_report_count': 26, 'declarations': ds})
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
    assert len(own) == 1247 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for p, ds in declarations().items() for _, n in ds]
    assert names == registration['names'] and len(names) == 26
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
    assert len(registered) == len(set(registered)) == len(actual) == 5591
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
    framework = 'preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/build/sections/02_framework.tex'
    framework_bytes = (Path('E:/codex-build/math') / framework).read_bytes().replace(b'\r\n', b'\n')
    assert not any(section['path'] == framework for section in fixed['sections'])
    fixed['sections'].append(dict(path=framework, normalized_sha256=hashlib.sha256(framework_bytes).hexdigest(), matches_pinned_git_object=True))
    for section in fixed['sections']:
        data = (Path('E:/codex-build/math') / section['path']).read_bytes().replace(b'\r\n', b'\n')
        pinned = subprocess.run(['git', '-C', 'E:/codex-build/math', 'show',
            fixed['fixed_openai_math_commit'] + ':' + section['path']], stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, check=True).stdout.replace(b'\r\n', b'\n')
        assert data == pinned and hashlib.sha256(data).hexdigest() == section['normalized_sha256']
    files = [{'path': f['path'], 'sha256': digest(f['path'])} for f in baseline['files']]
    files += [{'path': p, 'sha256': digest(p)} for p in MODULES]
    assert len(files) == len({f['path'] for f in files}) == 1265
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=22, new_definitions=4, new_structures=1, new_instances=0, new_axiom_reports=26, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True,
        axiom_free_reports=sorted(n for n, v in actual.items() if not v),
        new_axiom_free_reports=sorted(EXPECTED_NEW_AXIOM_FREE), full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-11', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. The preceding bounded count sampling audit was terminal-successfully rechecked and its authoritative manifest copied before new proof edits. All retained proof sources stay unchanged.', 'Integer and natural division are connected only after proving anchor divisibility. Rational division additionally requires actual positive anchor coefficients. The eventual master theorem obtains both facts from actual valid chain coefficients and ratios, and its rational identity uses their proved exact master scale equalities.', 'Positive natural-coordinate normalized forms use the maximum term with coefficient c/c=1 and nonnegative remaining terms. The natural toNat sum identity explicitly proves nonnegativity before eliminating toNat. Negative integer inputs are still permitted in the separate exact rational and scaled identities.', 'The selected principal map is injective by strict monotonicity. Restriction of piMass uses normalization of every actual unused coordinate from proved cutoff validity, rather than renormalizing or postulating selected independence. Arbitrary-test expectation equality follows from exact pushforward equality.', 'Finite image scales are identified by the exact original product formula and an injective image product. Adding-block transport uses all strict index orders and both nonempty tails. Actual hF.adding_scales retains the original W^w factor and common modulus.', 'Earlier selected principal indices lie before the current own padding index. Each cutoff squared is at least one, so the selected product is bounded by the full original padding auxiliary. The proof applies original gap growth to this actual bound, and uses earlier-gap divisibility to compare padding and principal gaps for cutoff growth.', 'The selected earlier-cutoff auxiliary uses squared cutoffs; this is stronger than the paper auxiliary with first powers. SelectedAdmissibleFamily describes the exact stronger constructed conditions. The raw law is the existing actual harmonic W-unit piMass; positivity of normalizers and total mass one are proved eventually, which is the asymptotic regime used by the paper.', 'The conditional model assembly preserves the identical e, heM, model, calibration, tests, count and common native manifold from the retained selected_color_product_counting theorem. It adds the admissibility proved from actual maskGeneratedMaster_conditions, with no replacement selection or extra parameter hypothesis.', 'Six new modules contain twenty-two theorems, four definitions and one Prop structure. The structure and its generated projections are covered by the transitive audit of the theorem constructing it. No new resource options, axioms, sorry, admit or native_decide are allowed. Full build and registered transitive kernel reports must finish successfully without warnings. Retained hashes and axiom sets must remain unchanged except root imports and registry.', 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional on those inverse inputs, the same selected native coloring models support both actual calibrated laws and bounded raw-coordinate count comparison at independent prescribed tolerances chosen before N. The actual selected original scales, own padding gaps, dyadic principal cutoffs and independent harmonic raw laws now satisfy the selected admissible family conditions. The original integer subset forms are proved to match the paper rational forms and to recover the actual scaled natural sums. Full Prediction output integration still needs selected-index relabeling of the complete block and count expressions and the precise ultrafilter-limit statements, as well as unconditional inverse inputs. Alignment and final ordered positive rapidly separated monochromatic extraction remain incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'], new_modules=MODULES, verified=summary, remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='02_framework admissible parameters and normalized forms; 05_prediction same-witness selected family integration')
    manifest = dict(baseline)
    manifest.update(date='2026-10-11', files=files, hindman_module_count=1247, pntplus_module_count=9,
        selected_axiom_report_count=5591, source_scan_module_count=1256,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=6, new_theorem_count=22,
            new_selected_report_count=26, retained_proof_sources_changed=False,
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
