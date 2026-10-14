"""Register and audit the common coloring Hilbert/native family and rho-S count replacement."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-alignment-schedule-execution'
OLD = 'round-alignment-future-scales'
EXPECTED_NEW_AXIOM_FREE = set()
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/AlignmentSchedulePaths.lean', 'Hindman168/AlignmentScheduleDenominators.lean', 'Hindman168/AlignmentScheduleExecution.lean', 'Hindman168/AlignmentCanonicalTargets.lean']
COMPONENTS = ['The actual relative multiplier catalogues at each planned pivot enumerate all possible incoming, intermediate and terminal global scales. A singleton-input executed pivot lands in the explicit next-step catalogue. Monotonicity supplies every stage scale to the global catalogue, and positivity of all incoming coordinates and choice parameters proves positivity of the complete state and terminal catalogues.', 'A single positive integer denominator is chosen for the entire multi-pivot schedule before any groups, actions, generators, palettes or initial centers. It covers each stage recurrence alphabet, all admitted jump letters and every original terminal test letter at every enumerated state or final scale. No action-specific or per-pivot denominator choices are substituted.', 'The full backward schedule now executes in order using independent per-pivot groups and initial centers. The actual recursive trace retains every fixed-pivot reachability witness, the unchanged chosen center in every final-scale request, and the shared final scale. The selected later scale product is proved a member of the precomputed future catalogue and exactly factors the final scale relative to the pivot endpoint. Future transport therefore supplies all final comparisons at the same frozen center.', 'All adding pairs are finitely enumerated from their original Fin n fields and ordering proofs. Every pair occurs, the list has no duplicates, all nonempty target alphabets occur, and filtering by target keeps the exact fixed order. The complete canonical request family and List.finRange n remove arbitrary external requests from the final theorem. Starting scales at one, the theorem chooses the whole schedule and its common positive denominator before all model data and proves simultaneous comparisons for every target and every sublist, with one chosen center for all targets at each pivot. This finite-word theorem remains conditional on HasAlignmentMonomialRecurrence.']
REMAINING = 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional Prediction includes actual admissible parameters, finite positive scale-list closure, all scale/color indices, globally unit-range common native observables and actual fixed-ultrafilter calibration and complete count limits. Conditional Alignment now has full backward planning and actual forward execution at all canonical pivots and targets, one common positive integer denominator covering all stage, jump and terminal letters, complete positive global scale catalogues and exact final-scale comparisons at each frozen pivot center. HasAlignmentMonomialRecurrence remains an explicit unproved input. Its genuine nilpotent recurrence existence proof, complete global positive palette-index closure and finite auxiliary prefix-slot planning, the integer residue/polynomial array realization and positive-probability Alignment bounds remain unproved. Final ordered positive rapidly separated monochromatic extraction is also incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'


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
    assert len(baseline['files']) == 1313
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for p, values in ds.items() for _, name in values]
    assert len(names) == len(set(names)) == 38
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 26
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 1313, 'modules': MODULES,
        'names': names, 'theorem_count': 26, 'selected_report_count': 38, 'declarations': ds})
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
    assert len(own) == 1299 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for p, ds in declarations().items() for _, n in ds]
    assert names == registration['names'] and len(names) == 38
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
    statement = read('Hindman168/AlignmentUniformPivotPlan.lean').split(
        'theorem alignment_uniform_pivot_plan', 1)[1].split(' := by', 1)[0]
    assert statement.index('∃ plan') < statement.index('∀ incoming') < statement.index('∃ q₀') < statement.index('∀ (G : Type')
    assert 'hrec : HasAlignmentMonomialRecurrence s' in statement
    assert 'alignmentScaleFrontier i (alignmentForwardOptions plan) incoming' in statement
    assert 'alignmentPivotReachable q₀ L plan b x' in statement
    statement = read('Hindman168/AlignmentFuturePivotPlan.lean').split(
        'theorem alignment_future_pivot_plan', 1)[1].split(' := by', 1)[0]
    assert statement.index('∃ plan') < statement.index('∀ incoming') < statement.index('∃ q₀') < statement.index('∀ (G : Type')
    assert 'hrec : HasAlignmentMonomialRecurrence s' in statement
    assert 'alignmentPivotReachable q₀ L plan b x' in statement
    assert '∀ d ∈ futures' in statement
    assert 'AlignmentPivotStageWorks.{u, v} s Color stage' in statement
    statement = read('Hindman168/AlignmentAllPivotPlanning.lean').split(
        'theorem alignment_all_pivot_plans_exist', 1)[1].split(' := by', 1)[0]
    assert 'hrec : HasAlignmentMonomialRecurrence s' in statement
    assert 'schedule.map AlignmentPlannedPivot.pivot = pivots' in statement
    assert 'alignmentAllPivotFits requests schedule' in statement
    assert 'AlignmentPivotStageWorks.{u, v} s Color stage' in statement
    statement = read('Hindman168/AlignmentScheduleExecution.lean').split(
        'theorem alignment_uniform_schedule', 1)[1].split(' := by', 1)[0]
    assert statement.index('∃ schedule') < statement.index('∀ incoming') < statement.index('∃ q₀') < statement.index('∀ (G : Fin n')
    assert 'hrec : HasAlignmentMonomialRecurrence s' in statement
    assert 'alignmentScheduleRealizes G X q₀ L palette requests centers schedule b final' in statement
    statement = read('Hindman168/AlignmentCanonicalTargets.lean').split(
        'theorem alignment_canonical_finite_word_plan', 1)[1].split(' := by', 1)[0]
    assert statement.index('∃ schedule') < statement.index('∃ q₀') < statement.index('∀ (G : Fin n')
    assert 'hrec : HasAlignmentMonomialRecurrence s' in statement
    assert 'schedule.map AlignmentPlannedPivot.pivot = List.finRange n' in statement
    assert '∀ i : Fin n, ∃ y : X i, ∀ T' in statement
    assert 'selected.Sublist (alignmentCanonicalTargetPairs n i T)' in statement
    assert 'alignmentScheduleRealizes G X q₀ L palette (alignmentCanonicalRequests n) centers' in statement
    assert 'alignmentScheduleLetters (alignmentCanonicalRequests n) planned' in statement
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
    assert len(registered) == len(set(registered)) == len(actual) == 5865
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
    assert len(files) == len({f['path'] for f in files}) == 1317
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=26, new_definitions=12, new_structures=0, new_instances=0, new_axiom_reports=38, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True,
        axiom_free_reports=sorted(n for n, v in actual.items() if not v),
        new_axiom_free_reports=sorted(EXPECTED_NEW_AXIOM_FREE), full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-11', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. The preceding future-scales round was rechecked successfully; its authoritative 1313-source manifest was copied before new proof edits. It had completed backward planning, while explicitly leaving combined forward execution and one global denominator open.', 'The global finite scale step multiplies each actual incoming tuple by each complete ones-input pivot multiplier. The retained singleton factor theorem proves every actual executed pivot endpoint lies in that catalogue. The global state catalogue includes all actual fixed-pivot stage scales before moving to the next global step. Its positivity follows from the genuine positive stage choice parameters.', 'The finite rational scalar set includes every stage target letter, every admitted jump letter and every original request letter. Clearing all these scalars at the union of global intermediate and terminal scales supplies one common integer before any group, action, assignment, palette or center. Including original terminal letters prevents a generator-only denominator statement from being used to claim integrality of unbudgeted final tests.', 'Forward execution recurses on the actual ordered schedule. At each pivot the previously proved finite plan produces a reachable endpoint and one successful center. The recursive tail returns its actual chosen future multiplier and exact factorization of the final scale. Transport with that same multiplier turns all future-augmented requests into original requests at the final scale and the unchanged pivot center.', 'The recursive outcome predicate ties every pivot jump to its input scale and input center, stores one actual successful center for all its requests, and uses one shared final scale throughout the whole tail. A separate comparison projection exposes simultaneous final comparisons for every plan in the list. The generic occurrence theorem allows repeated pivot labels; the canonical main caller uses each Fin n pivot exactly once in increasing List.finRange order.', 'Pair finiteness is proved by injectivity into its three original finite fields; proof fields are handled by proof irrelevance. The Fintype value is local and reducible, so no global new instance is installed. Finset.univ.toList fixes an order depending on n alone. Every actual pair is present once. The finite target-tail image contains exactly targets with a nonempty pair alphabet, and its order proof is derived from a real corresponding pair.', 'Canonical requests enumerate each target-tail subtype, and each uses all sublists of the exact ordered target pair list. Thus all subset tests are covered by the retained filtered-subset support theorem. Empty sublists are included. The final theorem proves one center per pivot that works for all target blocks and all selected sublists. The actual integer exponents are q0 times the original final-scale ratios, not assumed separate generators.', 'This closes the common-denominator and combined forward execution gaps in the abstract finite-word construction. It does not prove monomial nilpotent recurrence existence. The remaining global palette-index closure, bounded auxiliary prefix slots, actual integer model action and positive probability loss must still be connected before a complete Alignment principle or StrongConjecture can be claimed.', 'Four modules contain 26 theorems and 12 definitions, with all 38 declaration names selected for kernel audit. No new structures, instances, unproved axioms, proof holes, unsafe code or resource options are introduced. Strict focused checks, full build, exact selected axiom checks, unchanged retained hashes and final recheck must all terminate successfully before progress is recorded.', 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional Prediction includes actual admissible parameters, finite positive scale-list closure, all scale/color indices, globally unit-range common native observables and actual fixed-ultrafilter calibration and complete count limits. Conditional Alignment now has full backward planning and actual forward execution at all canonical pivots and targets, one common positive integer denominator covering all stage, jump and terminal letters, complete positive global scale catalogues and exact final-scale comparisons at each frozen pivot center. HasAlignmentMonomialRecurrence remains an explicit unproved input. Its genuine nilpotent recurrence existence proof, complete global positive palette-index closure and finite auxiliary prefix-slot planning, the integer residue/polynomial array realization and positive-probability Alignment bounds remain unproved. Final ordered positive rapidly separated monochromatic extraction is also incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'], new_modules=MODULES, verified=summary, remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='08_alignment common global denominator and actual multi-pivot execution for every canonical target and ordered subset test')
    manifest = dict(baseline)
    manifest.update(date='2026-10-11', files=files, hindman_module_count=1299, pntplus_module_count=9,
        selected_axiom_report_count=5865, source_scan_module_count=1308,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=4, new_theorem_count=26,
            new_selected_report_count=38, retained_proof_sources_changed=False,
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
