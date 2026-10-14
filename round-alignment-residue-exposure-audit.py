"""Register and audit the common coloring Hilbert/native family and rho-S count replacement."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-alignment-residue-exposure'
OLD = 'round-alignment-integer-residues'
EXPECTED_NEW_AXIOM_FREE = set()
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/AlignmentResidueRepresentative.lean', 'Hindman168/AlignmentRawExposure.lean', 'Hindman168/AlignmentExposedResidues.lean', 'Hindman168/AlignmentExposedArrayOffsets.lean']
COMPONENTS = ['The bounded full-modulus residue solution is unique. A canonical representative depends on the numerator, tail product and modulus alone, and is invariant when numerator and tail product change within their respective residue classes.', 'The raw exposure predicate fixes only earlier coordinates outside the target tail and only full-modulus residues inside that tail. It leaves all coordinates at and after the pivot unrestricted. Source blocks are disjoint from their own target tails. All earlier block products and all pair numerators have fixed full-modulus residues; own-target numerators are fixed as complete integers.', 'Actual pair residue data are now canonical functions of the actual master numerator and target tail product. Their positivity bounds, small-prime divisibility, full congruence, progression divisibility and integer identity are retained. The actual exposure fixes every pair residue and every finite numerical slot shift, including residues for other targets.', 'The exposure fixes target array residues at the original smooth modulus. The exact canonical progression increment is affine in the changing own-target tail product: its M-multiple changes by minus the tail-product change times the fixed residue. Summing all own-target coordinates gives the exact corresponding affine change in the entire numerical array progression.']
REMAINING = 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional Prediction includes actual admissible parameters, positive finite scale-list closure, common native unit observables and complete fixed-ultrafilter calibration and count limits. Conditional Alignment includes the canonical finite-word schedule, actual execution, positive palette-scale budgets, common positive denominator and certified actual auxiliary visits. Integer realization now proves the actual master pair scale relation, exact natural numerator with its original rational value, canonical bounded full-modulus residues, all required divisibilities, uniform eventual fixed-integer divisibility, finite numerical slot bounds and the numerical own-target array-letter identity. The actual earlier-variable exposure fixes every residue and slot shift, full own-target numerators and array residues; exact affine tail dependence of each progression and the whole own-target progression sum is proved. HasAlignmentMonomialRecurrence remains an explicit unproved input. Its genuine nilpotent recurrence proof, the actual native polynomial-array model action with its required nilpotence and translation compatibility, microcell boundary and point-law estimates, and positive-probability Alignment bounds remain unproved. Final ordered positive rapidly separated monochromatic extraction is incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'


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
    assert len(baseline['files']) == 1329
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for p, values in ds.items() for _, name in values]
    assert len(names) == len(set(names)) == 23
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 18
    assert sum(kind in {'def', 'abbrev'} for values in ds.values() for kind, _ in values) == 5
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 1329, 'modules': MODULES,
        'names': names, 'theorem_count': 18, 'selected_report_count': 23, 'declarations': ds})
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
    assert len(own) == 1315 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for p, ds in declarations().items() for _, n in ds]
    assert names == registration['names'] and len(names) == 23
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
    statement = read('Hindman168/AlignmentFiniteWordBudgets.lean').split(
        'theorem alignment_finite_word_budgets', 1)[1].split(' := by', 1)[0]
    assert statement.index('∃ schedule') < statement.index('∃ A') < statement.index('∃ q₀') < statement.index('∀ (G : Fin n')
    assert 'hrec : HasAlignmentMonomialRecurrence s' in statement
    assert 'schedule.map AlignmentPlannedPivot.pivot = List.finRange n' in statement
    assert 'FiniteScaleClosure (alignmentScheduleFinalScales schedule {fun _ => 1}) A' in statement
    assert '(∀ a ∈ A, 0 < a)' in statement
    assert 'alignmentScheduleRealizes G X q₀ L palette (alignmentCanonicalRequests n) centers' in statement
    assert 'alignmentScheduleSlotsRealizes G X q₀' in statement
    assert '∀ position' in statement and '(∀ i, position i (centers i) = 0)' in statement
    visits = read('Hindman168/AlignmentAuxiliaryWords.lean')
    assert 'Finset.Icc (min 0 z) (max 0 z)' in visits
    assert 'alignment_action_integer_translation' in visits
    residue = read('Hindman168/AlignmentMasterResidueData.lean')
    statement = residue.split('theorem alignmentMaster_eventual_residue_divisibility', 1)[1].split(' := by', 1)[0]
    assert statement.index('∀ᶠ w in atTop') < statement.index('∀ t : Fin n') < statement.index('∀ i : Fin n')
    assert 'MasterParameterConditions n A D F' in statement
    assert 'HasAlignmentMonomialRecurrence' not in residue
    exact = read('Hindman168/AlignmentIntegerResidues.lean')
    assert '((q : ℤ) - (t : ℤ) * ρ) / M' in exact
    assert 'Nat.exists_mul_mod_eq_of_coprime' in exact
    assert 'alignment_residue_progression_exact' in exact
    array = read('Hindman168/AlignmentIntegerArrayArguments.lean')
    assert 'if e.targetTail = T then u e * Δ e else 0' in array
    assert 'alignmentIntegerArrayArgument_own_letter' in array
    exposure = read('Hindman168/AlignmentRawExposure.lean')
    predicate = exposure.split('def alignmentRawExposure', 1)[1].split('theorem', 1)[0]
    assert "(∀ j, j < i → j ∉ T → t j = t' j)" in predicate
    assert "(∀ j ∈ T, Nat.ModEq L (t j) (t' j))" in predicate
    assert 'alignmentPair_source_disjoint_tail' in exposure
    representative = read('Hindman168/AlignmentResidueRepresentative.lean')
    assert 'alignment_bounded_residue_unique' in representative
    assert 'alignmentResidueRepresentative_congr' in representative
    fixed = read('Hindman168/AlignmentExposedResidues.lean')
    assert 'alignmentRawExposure_slot_shift_eq' in fixed
    offsets = read('Hindman168/AlignmentExposedArrayOffsets.lean')
    assert 'alignmentRawExposure_arrayProgression_difference' in offsets
    assert 'alignmentRawExposure_arrayResidue_eq' in offsets
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
    assert len(registered) == len(set(registered)) == len(actual) == 5967
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
    assert len(files) == len({f['path'] for f in files}) == 1333
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=18, new_definitions=5, new_structures=0, new_instances=0, new_axiom_reports=23, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True,
        axiom_free_reports=sorted(n for n, v in actual.items() if not v),
        new_axiom_free_reports=sorted(EXPECTED_NEW_AXIOM_FREE), full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-11', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. The preceding integer-residues round was rechecked successfully and its authoritative 1329-source manifest was copied before new proof edits. Retained proof sources and exact selected axiom sets remain fixed.', 'Coprime cancellation and the strict bounds below the full modulus prove uniqueness of the residue. The canonical representative is chosen from numerical q,t,L alone. Its congruence invariance therefore fixes an actual function rather than merely permitting a convenient fresh representative in each exposure.', 'The exposure matches the paper: exact values outside the selected tail are fixed only for earlier coordinates, and residues modulo L are fixed inside the selected tail. It does not fix the pivot or later coordinates and does not incorrectly fix the exact values inside the target tail.', 'All pair sources and target tails lie before the pivot, so their products have fixed residues. Exact natural numerator coefficients depend only on the fixed denominator, w and pair. Each source block is disjoint from its own target tail, so each own-target full integer numerator is fixed. Numerators for other targets are only claimed fixed modulo L.', 'Canonical residues retain the actual master bounds, divisibilities, full congruence and signed integer identity by uniqueness of the previously constructed bounded solution. Full smooth-modulus coprimality comes from the genuine retained master arithmetic, not an assumed congruence solution. All pair residues and the entire finite slot sum are invariant under exposure.', 'The target array residue uses integer remainder because the slot shift is signed. Reduction from L to M follows from M dividing L. Fixed tail residues consequently fix r-star and every r-v for fixed pivot residue and slot shift. The unknown microcell origin is not fixed by this arithmetic theorem.', 'The exact progression difference is affine in the changing target tail product; full own-target numerator and canonical residue invariance are used. Summation includes precisely the coordinates whose target tail is the exposed T. Other-target progression terms are not asserted to have this affine formula.', 'Four modules contain 18 theorems and 5 definitions; all 23 declarations are selected for kernel audit. No proof holes, new axioms, structures, global instances, unsafe code or resource changes are introduced. Strict focused checks, full build, kernel checking, exact retained-source and axiom comparisons and final recheck must terminate successfully.', 'These are arithmetic exposure and numerical array-coefficient results. They do not prove the conditional sampling domination, boundary error, ordinary polynomial logarithm of a native model array, nilpotent model action, face invariance or positive-probability Alignment.', 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional Prediction includes actual admissible parameters, positive finite scale-list closure, common native unit observables and complete fixed-ultrafilter calibration and count limits. Conditional Alignment includes the canonical finite-word schedule, actual execution, positive palette-scale budgets, common positive denominator and certified actual auxiliary visits. Integer realization now proves the actual master pair scale relation, exact natural numerator with its original rational value, canonical bounded full-modulus residues, all required divisibilities, uniform eventual fixed-integer divisibility, finite numerical slot bounds and the numerical own-target array-letter identity. The actual earlier-variable exposure fixes every residue and slot shift, full own-target numerators and array residues; exact affine tail dependence of each progression and the whole own-target progression sum is proved. HasAlignmentMonomialRecurrence remains an explicit unproved input. Its genuine nilpotent recurrence proof, the actual native polynomial-array model action with its required nilpotence and translation compatibility, microcell boundary and point-law estimates, and positive-probability Alignment bounds remain unproved. Final ordered positive rapidly separated monochromatic extraction is incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'], new_modules=MODULES, verified=summary, remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='08_alignment conditional face invariance: exposed residue data and exact affine progression dependence')
    manifest = dict(baseline)
    manifest.update(date='2026-10-11', files=files, hindman_module_count=1315, pntplus_module_count=9,
        selected_axiom_report_count=5967, source_scan_module_count=1324,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=4, new_theorem_count=18,
            new_selected_report_count=23, retained_proof_sources_changed=False,
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
