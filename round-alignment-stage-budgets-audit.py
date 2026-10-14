"""Register and audit the common coloring Hilbert/native family and rho-S count replacement."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-alignment-stage-budgets'
OLD = 'round-alignment-finite-alternatives'
EXPECTED_NEW_AXIOM_FREE = set()
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/AlignmentFiniteWordAlphabet.lean', 'Hindman168/AlignmentMonomialRecurrenceInput.lean', 'Hindman168/AlignmentChoicePredecessors.lean', 'Hindman168/AlignmentStageAdvance.lean', 'Hindman168/AlignmentScalePaths.lean', 'Hindman168/AlignmentPlanFiniteScales.lean']
COMPONENTS = ['Every actual finite rational-letter word family has an explicit finite alphabet. Encoding into the subtype of occurring letters and decoding preserve the complete ordered word and the exact finite family. The still unproved monomial recurrence input is stated on finite alphabets and palettes. Its proved consequence gives actual rational-letter target choices uniformly before all groups, actions, scales, integral exponents and centers.', 'Predecessor leading and word budgets are finite unions over every alternative. One requirement on these unions preserves the original comparison for every chosen positive update and jump. Positive input leading indices remain positive throughout the backward budgets. The ordered action and actual compensating scales are retained.', 'A proved forward-stage theorem simultaneously establishes its own target, retains positive scales and preserves all previously specified target comparisons. The finite table is quantified before every group, state space, action, incoming scale, generator, palette and center. The recurrence, local integrality and predecessor requirements remain explicit inputs; no complete multi-target or multi-pivot recursion is asserted.', 'An actual finite stage schedule has finite rational scale frontiers and an explicit catalogue of all incoming, intermediate and terminal tuples. All choices are represented by the original compensating updates. Positivity, concatenation, monotonicity and prefix coverage are proved, so every stage uses a tuple in the finite catalogue.', 'All enumerated path scales and any prescribed finite letter set share one positive integer denominator. The actual finite palette index catalogue is positive for positive incoming tuples, positive choices and positive leading factors. Enlarging it by every subset product of every terminal tuple gives the exact FiniteScaleClosure required by Prediction, including all consulted intermediate palette indices.']
REMAINING = 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional Prediction includes actual admissible parameters, finite positive scale-list closure, all scale/color indices, globally unit-range common native observables and actual fixed-ultrafilter calibration and complete count limits. Conditional Alignment now gives actual finite target word choices, all-alternative predecessor budgets and simultaneous forward-stage advancement; finite schedules have proved complete scale catalogues, common denominators and positive Prediction palette closure. HasAlignmentMonomialRecurrence is an explicit unproved input. Its genuine nilpotent recurrence existence proof, full backward/forward construction across all targets and pivots, finite auxiliary slot planning and positive-probability integer Alignment realization remain unproved. Final ordered positive rapidly separated monochromatic extraction is also incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'


def declarations():
    ds = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|instance)\s+([A-Za-z][A-Za-z0-9_\.]*)', old.lean_code(read(p)), re.M) for p in MODULES}
    return ds


def check_focused():
    results = obj(PREFIX + '-focused-results.json')
    assert [r['module'] for r in results] == MODULES
    for r in results:
        assert r['terminal'] and r['exit_code'] == 0
        assert r['command'] == ['lake', 'env', 'lean', '-DautoImplicit=false', r['module']]
        assert digest(r['module']) == r['source_sha256']
        assert digest(r['log']) == r['log_sha256']
        assert not Path(r['log']).read_bytes().strip()


def register():
    check_focused()
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 1297
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for p, values in ds.items() for _, name in values]
    assert len(names) == len(set(names)) == 39
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 27
    assert sum(kind in {'def', 'abbrev'} for values in ds.values() for kind, _ in values) == 12
    assert not any(kind == 'instance' for values in ds.values() for kind, _ in values)
    assert sum(len(re.findall(r'^\s*structure\s+', old.lean_code(read(p)), re.M)) for p in MODULES) == 0
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 1297, 'modules': MODULES,
        'names': names, 'theorem_count': 27, 'selected_report_count': 39, 'declarations': ds})
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
    check_focused()
    baseline = obj(PREFIX + '-baseline.json')
    registration = obj(PREFIX + '-registration.json')
    changed = [f['path'] for f in baseline['files'] if digest(f['path']) != f['sha256']]
    assert changed == ['Hindman168.lean', 'Verification.lean']
    own = sorted(Path('Hindman168').glob('*.lean'))
    pnt = sorted(Path('PrimeNumberTheoremAnd').rglob('*.lean'))
    assert len(own) == 1285 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for p, ds in declarations().items() for _, n in ds]
    assert names == registration['names'] and len(names) == 39
    for path, name, existential in [
        ('Hindman168/AlignmentFiniteRecurrenceTransfer.lean', 'alignment_uniform_action_alternatives', '∃ alternatives'),
        ('Hindman168/AlignmentTargetAlternatives.lean', 'alignment_target_finite_alternatives', '∃ alternatives'),
        ('Hindman168/AlignmentJumpTemplates.lean', 'alignment_target_finite_word_choices', '∃ choices')]:
        statement = read(path).split('theorem ' + name, 1)[1].split(' := by', 1)[0]
        assert statement.index(existential) < statement.index('∀ (G : Type')
        assert '[Group G]' in statement and '[MulAction G X]' in statement
        assert '{G X' not in statement
    for path, name in [
        ('Hindman168/AlignmentMonomialRecurrenceInput.lean', 'alignment_actual_target_choices'),
        ('Hindman168/AlignmentStageAdvance.lean', 'alignment_stage_advance')]:
        statement = read(path).split('theorem ' + name, 1)[1].split(' := by', 1)[0]
        assert statement.index('∃ choices') < statement.index('∀ (G : Type')
        assert 'hrec : HasAlignmentMonomialRecurrence s' in statement
        assert '(Int.castRingHom ℚ).range' in statement
    recurrence = read('Hindman168/AlignmentMonomialRecurrenceInput.lean')
    assert 'def HasAlignmentMonomialRecurrence' in recurrence
    assert not re.search(r'(?:theorem|lemma)\s+HasAlignmentMonomialRecurrence', recurrence)
    prior = read('Hindman168/PrincipalPredictionModels.lean')
    assembled = read('Hindman168/PrincipalPredictionModelsWithLimits.lean')
    prior_statement = prior[prior.index('theorem principal_prediction_models'):].split(' := by\n', 1)[0]
    assembled_statement = assembled[assembled.index('theorem principal_prediction_models_with_limits'):].split(' := by\n', 1)[0]
    limit_field = ('          PrincipalPredictionLimitData (m := m) M e F U cap countTolerance a χ color\n'
        '            (fun T b γ w y => (model T b γ).val w y) ∧\n')
    assert assembled_statement.count(limit_field) == 1
    assert assembled_statement.replace(limit_field, '', 1).replace(
        'principal_prediction_models_with_limits', 'principal_prediction_models', 1) == prior_statement
    finite_source = read('Hindman168/FiniteScalePredictionModels.lean')
    finite_statement = finite_source[finite_source.index('theorem finite_scale_prediction_models'):].split(' := by\n', 1)[0]
    specialized = assembled_statement.replace(
        'theorem principal_prediction_models_with_limits (ι : Type*) [Fintype ι]',
        'theorem finite_scale_prediction_models (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a)', 1)
    specialized = re.sub(r'\bι\b', '(ScaleColorIndex A r)', specialized)
    old_quantifiers = ('      ∀ (a : (ScaleColorIndex A r) → ℚ) (_ha : ∀ γ, 0 < a γ)\n'
        '        (χ : ℕ → Fin r) (color : (ScaleColorIndex A r) → Fin r),\n')
    assert specialized.count(old_quantifiers) == 1
    specialized = specialized.replace(old_quantifiers,
        '      let a := scaleColorFactor A r\n      let color := scaleColorValue A r\n      ∀ χ : ℕ → Fin r,\n', 1)
    assert finite_statement == specialized
    unit_source = read('Hindman168/FiniteScaleNativeUnitModels.lean')
    unit_statement = unit_source[unit_source.index('theorem finite_scale_prediction_models_unit_observables'):].split(' := by\n', 1)[0]
    unit_field = '                (∀ w p z, 0 ≤ obs w p z ∧ obs w p z ≤ 1) ∧\n'
    assert unit_statement.count(unit_field) == 1
    assert unit_statement.replace(unit_field, '', 1).replace(
        'finite_scale_prediction_models_unit_observables', 'finite_scale_prediction_models', 1) == finite_statement
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
    assert len(registered) == len(set(registered)) == len(actual) == 5772
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert all(actual[n] == v for n, v in previous.items())
    assert all(v <= old.ALLOWED for v in actual.values())
    assert {n for n, v in actual.items() if not v} == EXPECTED_NEW_AXIOM_FREE | {n for n, v in previous.items() if not v} | {'Hindman168.intervalResidueParent', 'Hindman168.completeResidueCellPoint', 'Hindman168.integerCubeResidueShift', 'Hindman168.admissible_option_selection_none'}
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
    assert len(files) == len({f['path'] for f in files}) == 1303
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=27, new_definitions=12, new_structures=0, new_instances=0, new_axiom_reports=39, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True,
        axiom_free_reports=sorted(n for n, v in actual.items() if not v),
        new_axiom_free_reports=sorted(EXPECTED_NEW_AXIOM_FREE), full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-11', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. The previous alignment-finite-alternatives round was terminal-successfully rechecked. The authoritative 1297-source manifest was copied before new proof edits as round-alignment-pivot-plans-baseline.json and retained identically under the current round name. All retained proof sources remain fixed.', 'The finite alphabet is constructed from the exact biUnion of every word toFinset. Attached-list encoding retains repeated letters and order. Both individual decode and complete finite-family decode are proved, so no theorem for a surrogate word family is substituted for the actual rational words.', 'HasAlignmentMonomialRecurrence is a Prop definition, not an axiom or a theorem asserting existence. It universally quantifies finite alphabets, finite palettes, positive degrees and actual free step-s groups. The actual target theorem explicitly assumes it and uses the already proved exact signed-word table. Its finite alphabet is countable by the retained quotient countability theorem, matching the paper citation scope.', 'Each old budget is the actual finite union over all possible next choices. Exact subset inclusions reduce the union requirement to the retained ordered predecessor preservation theorem. Leading positivity is proved from positive choices and the actual finite product of positive rational multipliers, including empty blocks.', 'The stage theorem preserves arbitrary finite previous target sets and palette maps, with no action commutativity or jump-fixing premise. One selected choice establishes the new target and all old targets simultaneously. Local old-scale integrality remains explicit; the denominator theorem supplies it once a complete finite schedule and letter set have been constructed.', 'Scale paths enumerate each finite stage choice at the exact current tuple, rather than replacing the updates by a scalar bound or selecting an already successful path. Separate catalogues retain every intermediate tuple and the terminal frontier. Concatenation and prefix containment ensure common denominators can be chosen before execution. This round proves these facts for a fixed pivot; plans at different pivots and future-multiplier terminal budgets are still missing.', 'The palette catalogue is the actual a times block product at every enumerated tuple and every listed block and leading factor. Its enlargement contains the complete terminal subset-product family and proves FiniteScaleClosure on the actual frontier. Positive hypotheses are proved through the original scale updates. No native model or positive recurrence probability is selected by these catalogue lemmas.', 'Six new modules contain twenty-seven theorems and twelve definitions or abbreviations, with thirty-nine selected kernel reports. New modules use no resource options, proof holes, unsafe implementation or new axioms. Full build, full kernel audit and retained-source/dependency comparisons must finish successfully before recording progress.', 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional Prediction includes actual admissible parameters, finite positive scale-list closure, all scale/color indices, globally unit-range common native observables and actual fixed-ultrafilter calibration and complete count limits. Conditional Alignment now gives actual finite target word choices, all-alternative predecessor budgets and simultaneous forward-stage advancement; finite schedules have proved complete scale catalogues, common denominators and positive Prediction palette closure. HasAlignmentMonomialRecurrence is an explicit unproved input. Its genuine nilpotent recurrence existence proof, full backward/forward construction across all targets and pivots, finite auxiliary slot planning and positive-probability integer Alignment realization remain unproved. Final ordered positive rapidly separated monochromatic extraction is also incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'], new_modules=MODULES, verified=summary, remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='08_alignment finite alphabet, all-alternative predecessor budgets, simultaneous stage advancement, finite scale paths and uniform denominator/palette planning')
    manifest = dict(baseline)
    manifest.update(date='2026-10-11', files=files, hindman_module_count=1285, pntplus_module_count=9,
        selected_axiom_report_count=5772, source_scan_module_count=1294,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=6, new_theorem_count=27,
            new_selected_report_count=39, retained_proof_sources_changed=False,
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
