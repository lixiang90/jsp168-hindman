"""Register and audit the common coloring Hilbert/native family and rho-S count replacement."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-native-finite-product-model'
OLD = 'round-native-product-lie-model'
EXPECTED_NEW_AXIOM_FREE = {'Hindman168.nativeFiniteProduct', 'Hindman168.nativeFiniteProductChartModel'}
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/NativeFiniteProductSpaces.lean', 'Hindman168/NativeFiniteProductManifold.lean', 'Hindman168/NativeFiniteProductCoordinates.lean', 'Hindman168/NativeFiniteProductLieMap.lean', 'Hindman168/NativeFiniteProductExponential.lean', 'Hindman168/AlignmentNativeFiniteEvaluationImage.lean', 'Hindman168/AlignmentNativeFiniteImageSubgroup.lean']
COMPONENTS = ['Nonempty finite products are genuine recursively iterated products of the original group and tangent model, with n+1 factors. Their actual group, topology, normed real vector space, completeness, finite dimension, Hausdorffness, nilpotence and connectedness structures are constructed recursively, with no global instances.', 'The finite product has actual recursive product charts and models with corners, with the original manifold chart at every factor. The chart model retains the required ModelProd manifold tags. Its original native Lie group and boundaryless structures are proved, and actual product contractibility gives simply connectedness for the original simply connected nilpotent groups.', 'Every actual finite product coordinate is explicitly constructed, and equality at all n+1 original coordinates determines the product. The last and prefix coordinate equations are proved for this same recursive product.', 'A finite family of original Lie evaluation homomorphisms is assembled into a genuine Lie homomorphism to the native Lie algebra of the actual finite group product. The previously proved actual native binary product Lie equivalence is used recursively. Its original coordinates are exactly the supplied evaluations, and joint evaluation injectivity implies injectivity of this native homomorphism.', 'Every coordinate of the actual finite product exponential is the original exponential of that original tangent coordinate. The exact original global logarithm coordinate formula follows from the actual exponential comparison and inverse laws. These formulas also hold for coefficient images under the constructed native Lie homomorphism.', 'The entire original native polynomial-array coefficient Lie algebra embeds into the native Lie algebra of one actual finite original-group product by a fixed finite family of actual integer evaluations. The previously proved finite separation set is augmented by the zero input, genuinely enumerated by Fin(n+1), and used to prove the embedding injective. This also covers an empty original selection and a zero coefficient algebra.', 'The full finite evaluation image integrates to a genuine subgroup of the actual finite original-group product. Every element is the actual original-product exponential of an array coefficient vector, with exactly the original integer-evaluation exponentials at each selected coordinate. For original simply connected groups this coefficient parametrization is injective and the subgroup is closed, contractible and simply connected. Compatibility at all other integer evaluations and the specified array lattice still require proofs.']
REMAINING = 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional Prediction includes actual admissible parameters, positive finite scale-list closure, common native unit observables and complete fixed-ultrafilter calibration and count limits. Conditional Alignment includes the canonical finite-word schedule, actual execution, positive palette-scale budgets, common positive denominator and certified actual auxiliary visits. Integer realization now proves the actual master pair scale relation, exact natural numerator with its original rational value, canonical bounded full-modulus residues, all required divisibilities, uniform eventual fixed-integer divisibility, finite numerical slot bounds and the numerical own-target array-letter identity. The actual earlier-variable exposure fixes every residue and slot shift, full own-target numerators and array residues; exact affine tail dependence of each progression and the whole own-target progression sum is proved. Concrete integer-input polynomial array groups, their common nilpotence bound, input translations, pointwise lattice coset evaluation and exact affine model linear orbits are constructed. The genuine original native Lie polynomial-array coefficient algebra, bracket closure, high-degree cutoff and finite dimension are now proved; literal Lie evaluation homomorphisms and their lower-central compatibility are constructed. The same-step lower-central cutoff of the genuine array Lie algebra, injectivity of all integer evaluations and simultaneous coefficient recovery by one fixed finite integer evaluation set are now proved, including for the original native model. The actual binary product native Lie algebra, componentwise original exponential and global logarithm, and integration and inherited topology of every product Lie subalgebra are now proved. The complete native array coefficient algebra now embeds by one fixed finite family of integer inputs into the native Lie algebra of an actual finite original-group product. Its finite evaluation image integrates to a closed contractible simply connected subgroup, uniquely parameterized by coefficient exponentials. Compatibility of reconstructed multiplication with every remaining integer evaluation, construction and identification of the full native array group, its specified discrete cocompact lattice and smooth quotient evaluation remain unproved. HasAlignmentMonomialRecurrence remains an explicit unproved input. Its genuine nilpotent recurrence proof, the actual native polynomial-array model action with its required nilpotence and translation compatibility, microcell boundary and point-law estimates, and positive-probability Alignment bounds remain unproved. Final ordered positive rapidly separated monochromatic extraction is incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'


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
    assert len(baseline['files']) == 1356
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for p, values in ds.items() for _, name in values]
    assert len(names) == len(set(names)) == 39
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 26
    assert sum(kind in {'def', 'abbrev'} for values in ds.values() for kind, _ in values) == 13
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 1356, 'modules': MODULES,
        'names': names, 'theorem_count': 26, 'selected_report_count': 39, 'declarations': ds})
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
    assert len(own) == 1345 and len(pnt) == 9
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
    array = read('Hindman168/AlignmentPolynomialArrayGroup.lean')
    assert 'Subgroup.closure (alignmentPolynomialArrayGenerators σ G)' in array
    assert 'p.totalDegree ≤ j + 1' in array
    assert 'alignmentPolynomialArrayGroup_lowerCentral_bot' in array
    assert 'hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥' in array
    lattice = read('Hindman168/AlignmentPolynomialArrayLattice.lean')
    assert 'Subgroup.pi Set.univ' in lattice
    assert 'Quotient.lift' in lattice
    assert 'alignmentPolynomialArrayCosetTranslation_evaluation' in lattice
    assert 'CompactSpace' not in lattice and '.Normal' not in lattice
    model = read('Hindman168/AlignmentPolynomialModelArrays.lean')
    assert 'alignmentPolynomialModelOrbit_linear' in model
    assert 'alignmentConstantArray (g ^ t) ^ ℓ' in model
    brackets = read('Hindman168/AlignmentLieLowerCentralBrackets.lean')
    assert 'LieModule.lowerCentralSeries R L L (j + k + 1)' in brackets
    assert 'Submodule.span_induction' in brackets and 'rw [lie_lie]' in brackets
    assert 'LieModule.antitone_lowerCentralSeries' in brackets
    coefficients = read('Hindman168/AlignmentGradedLiePolynomialArrays.lean')
    assert 'd.sum (fun _ n => n) - 1' in coefficients
    assert 'LieAlgebra.ExtendScalars.bracket_tmul' in coefficients
    assert 'Submodule.span_induction₂' in coefficients
    finite = read('Hindman168/AlignmentLieArrayFiniteDimension.lean')
    assert '(MvPolynomial.restrictTotalDegree σ R s).subtype.rTensor L' in finite
    assert 'alignmentLieArrayGenerator_highDegree_zero' in finite
    assert 'Submodule.finiteDimensional_of_le' in finite
    evaluation = read('Hindman168/AlignmentLieArrayEvaluation.lean')
    assert 'TensorProduct.lift' in evaluation and 'MvPolynomial.aeval u' in evaluation
    assert 'LieIdeal.map_lowerCentralSeries_le' in evaluation
    native = read('Hindman168/AlignmentNativeLieArrayCoefficients.lean')
    assert 'GroupLieAlgebra I G' in native
    assert 'nativeLieLowerCentral_nilpotencyClass_bot' in native
    assert 'inferInstanceAs (FiniteDimensional ℝ E)' in native
    layers = read('Hindman168/AlignmentLieTensorLayers.lean')
    assert 'LieModule.lowerCentralSeries R L L k' in layers
    assert 'alignmentLieTensorLayer_bracket_next' in layers
    assert 'TensorProduct.induction_on' in layers
    cutoff = read('Hindman168/AlignmentLieArrayNilpotence.lean')
    assert 'LieIdeal.bot_of_map_eq_bot hf' in cutoff
    assert 'nativeLieLowerCentral_nilpotencyClass_bot' in cutoff
    separation = read('Hindman168/AlignmentLieArrayIntegerSeparation.lean')
    assert 'TensorProduct.equivFinsuppOfBasisRight' in separation
    assert 'MvPolynomial.funext_set' in separation
    assert 'Set.infinite_range_of_injective Int.cast_injective' in separation
    selection = read('Hindman168/AlignmentFiniteEvaluationSelection.lean')
    assert 'IsArtinian.set_has_minimal' in selection
    assert '⨅ i ∈ S, (f i).ker' in selection
    assert 'alignmentLiePolynomialArrays_finiteDimensional' in selection
    embedding = read('Hindman168/AlignmentLieArrayFiniteEmbedding.lean')
    assert 'alignmentLieArrayFiniteEvaluation_exists_injective' in embedding
    assert 'alignmentLieArrayFiniteEvaluation_bracket' in embedding
    native = read('Hindman168/AlignmentNativeLieArrayFiniteEvaluations.lean')
    assert 'GroupLieAlgebra I G' in native
    assert 'nativeLieLowerCentral_nilpotencyClass_bot' in native
    product = read('Hindman168/NativeProductLieAlgebra.lean')
    assert 'nativeSmoothHom_bracket' in product and 'mfderiv_fst' in product
    assert 'GroupLieAlgebra (I.prod J) (G × K)' in product
    exponential = read('Hindman168/NativeProductExponential.lean')
    assert 'nativeLieExponential_map' in exponential
    assert 'nativeProductExponential_eq' in exponential
    logarithm = read('Hindman168/NativeProductGlobalLogarithm.lean')
    assert 'nativeLieGroup_contractible' in logarithm
    assert 'nativeProductGroup_simplyConnected' in logarithm
    assert 'nativeLieExponential_injective' in logarithm
    subgroup = read('Hindman168/NativeProductLieSubgroup.lean')
    assert 'nativeLieSubalgebraSubgroup (I := I.prod J)' in subgroup
    assert 'nativeProductLieSubgroup_globalLogarithm_iff' in subgroup
    model = read('Hindman168/NativeProductLieModel.lean')
    assert 'Submodule ℝ (E × F) := S.toSubmodule' in model
    assert 'nativeProductLieModel_map_eq' in model
    topology = read('Hindman168/NativeProductLieTopology.lean')
    assert 'nativeProductLieModel S ≃ₜ nativeProductLieSubgroup S' in topology
    assert 'continuous_subtype_val' in topology
    assert 'V.convex.contractibleSpace' in topology
    spaces = read('Hindman168/NativeFiniteProductSpaces.lean')
    assert '| n + 1 => nativeFiniteProduct X n × X' in spaces
    assert 'nativeFiniteProductIsNilpotent' in spaces
    manifold = read('Hindman168/NativeFiniteProductManifold.lean')
    assert 'ModelProd (nativeFiniteProductChartModel X n) X' in manifold
    assert 'nativeFiniteProductCorners I n' in manifold
    assert 'nativeLieGroup_contractible' in manifold
    coordinates = read('Hindman168/NativeFiniteProductCoordinates.lean')
    assert 'Fin.lastCases' in coordinates
    assert 'nativeFiniteProductCoordinate_injective' in coordinates
    maps = read('Hindman168/NativeFiniteProductLieMap.lean')
    assert 'nativeProductLieEquiv' in maps and '.symm.toLieHom.comp' in maps
    assert 'nativeFiniteProductLieMap_injective' in maps
    exponential = read('Hindman168/NativeFiniteProductExponential.lean')
    assert 'nativeProductExponential_fst' in exponential
    assert 'nativeFiniteProductGlobalLogarithm_coordinate' in exponential
    embedding = read('Hindman168/AlignmentNativeFiniteEvaluationImage.lean')
    assert 'alignmentNativeLieArray_finite_integer_embedding' in embedding
    assert 'insert 0 S' in embedding and 'Fintype.equivFin T' in embedding
    assert 'nativeFiniteProductLieMap_injective' in embedding
    image = read('Hindman168/AlignmentNativeFiniteImageSubgroup.lean')
    assert 'nativeLieSubalgebraSubgroup (I := nativeFiniteProductCorners I n)' in image
    assert 'LieHom.mem_range' in image
    assert 'alignmentNativeFiniteImage_exists' in image
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
    assert len(registered) == len(set(registered)) == len(actual) == 6102
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
    assert len(files) == len({f['path'] for f in files}) == 1363
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=26, new_definitions=13, new_structures=0, new_instances=0, new_axiom_reports=39, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True,
        axiom_free_reports=sorted(n for n, v in actual.items() if not v),
        new_axiom_free_reports=sorted(EXPECTED_NEW_AXIOM_FREE), full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-11', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. The preceding binary-product round was authoritatively rechecked and its 1356-source manifest was copied before new proof edits. Retained proof sources and exact selected axiom sets remain fixed.', 'The original finite product group, tangent model and chart model are constructed recursively. The n=0 case is one original factor, rather than an empty product; adding the zero input makes the actual selected evaluation family nonempty. All recursively constructed structures are locally installed definitions or proved propositions. No supplied finite-product Lie group or simply-connectedness premise is introduced.', 'The chart model uses the actual ModelProd tags at every recursive step. It is not assigned a guessed chart structure on a plain function type. The actual product chart, model with corners, Lie group and boundaryless structures are checked together; contractibility of the original factors proves product simply connectedness.', 'The finite Lie evaluation map is recursively composed through the proved native binary product Lie equivalence. Each coordinate equals the corresponding original Lie evaluation, and actual joint injectivity transfers to the native homomorphism. No point separation or bracket comparison is assumed for the array algebra.', 'The exact original exponential formulas use the retained actual binary-product exponential theorem. The global logarithm coordinate formula uses original exponential injectivity and the actual global inverse identities. Neither BCH functoriality nor a replacement exponential is introduced.', 'The finite evaluation selection is the retained proven fixed set. Augmentation by the zero integer input and a genuine finite equivalence enumerate it, even when the original set is empty. Every original selected evaluation is recovered through this equivalence, so the retained full coefficient separation proves injectivity for all coefficient vectors simultaneously.', 'The finite image is an actual Lie subalgebra range in the actual finite-product native Lie algebra. The retained Picard logarithm subgroup proof integrates it. Actual range membership supplies coefficient preimages; native exponential injectivity and coefficient embedding injectivity prove their uniqueness. The same actual subgroup is closed, contractible and simply connected.', 'This does not yet identify the finite image subgroup with all-integer arrays under pointwise multiplication. Compatibility with unselected integer evaluations still requires an argument, as do the specified lattice discreteness, cocompactness and smooth quotient maps. The main StrongConjecture, inverse input and recurrence input remain unproved.', 'Seven new modules contain 26 theorems and 13 definitions, all 39 declarations selected for kernel audit. No proof holes, new axioms, structures, global instances, unsafe code or resource settings are introduced. Strict focused checks, full build, kernel checks, retained-source and exact-axiom comparisons and final recheck must terminate successfully.', 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional Prediction includes actual admissible parameters, positive finite scale-list closure, common native unit observables and complete fixed-ultrafilter calibration and count limits. Conditional Alignment includes the canonical finite-word schedule, actual execution, positive palette-scale budgets, common positive denominator and certified actual auxiliary visits. Integer realization now proves the actual master pair scale relation, exact natural numerator with its original rational value, canonical bounded full-modulus residues, all required divisibilities, uniform eventual fixed-integer divisibility, finite numerical slot bounds and the numerical own-target array-letter identity. The actual earlier-variable exposure fixes every residue and slot shift, full own-target numerators and array residues; exact affine tail dependence of each progression and the whole own-target progression sum is proved. Concrete integer-input polynomial array groups, their common nilpotence bound, input translations, pointwise lattice coset evaluation and exact affine model linear orbits are constructed. The genuine original native Lie polynomial-array coefficient algebra, bracket closure, high-degree cutoff and finite dimension are now proved; literal Lie evaluation homomorphisms and their lower-central compatibility are constructed. The same-step lower-central cutoff of the genuine array Lie algebra, injectivity of all integer evaluations and simultaneous coefficient recovery by one fixed finite integer evaluation set are now proved, including for the original native model. The actual binary product native Lie algebra, componentwise original exponential and global logarithm, and integration and inherited topology of every product Lie subalgebra are now proved. The complete native array coefficient algebra now embeds by one fixed finite family of integer inputs into the native Lie algebra of an actual finite original-group product. Its finite evaluation image integrates to a closed contractible simply connected subgroup, uniquely parameterized by coefficient exponentials. Compatibility of reconstructed multiplication with every remaining integer evaluation, construction and identification of the full native array group, its specified discrete cocompact lattice and smooth quotient evaluation remain unproved. HasAlignmentMonomialRecurrence remains an explicit unproved input. Its genuine nilpotent recurrence proof, the actual native polynomial-array model action with its required nilpotence and translation compatibility, microcell boundary and point-law estimates, and positive-probability Alignment bounds remain unproved. Final ordered positive rapidly separated monochromatic extraction is incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed.'], new_modules=MODULES, verified=summary, remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a', reference_scope='08_alignment actual native finite product Lie group and integration of the full finite integer evaluation image')
    manifest = dict(baseline)
    manifest.update(date='2026-10-11', files=files, hindman_module_count=1345, pntplus_module_count=9,
        selected_axiom_report_count=6102, source_scan_module_count=1354,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=7, new_theorem_count=26,
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
