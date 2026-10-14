import Hindman168.AlignmentNativeJointModelOrbit

namespace Hindman168
open scoped Manifold ContDiff BigOperators

attribute [local instance 10] nativeFiniteProductTopologicalSpace
attribute [local instance] nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

variable {ι : Type*} {σ E H G : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, TopologicalSpace (H i)]
  {I : ∀ i, ModelWithCorners ℝ (E i) (H i)}
  [∀ i, TopologicalSpace (G i)] [∀ i, ChartedSpace (H i) (G i)] [∀ i, Group (G i)]
  [∀ i, LieGroup (I i) ∞ (G i)] [∀ i, BoundarylessManifold (I i) (G i)]
  [∀ i, T2Space (G i)] [∀ i, Group.IsNilpotent (G i)]
  [∀ i, ConnectedSpace (G i)] [∀ i, SimplyConnectedSpace (G i)]
  (n : ι → ℕ) (u : ∀ i, Fin (n i + 1) → σ i → ℤ)
  (hu : ∀ i, Function.Injective (alignmentNativeFiniteEvaluation (E := E i) (I := I i) (G := G i) (n i) (u i)))

noncomputable def alignmentNativeJointArrayTranslation (v : ∀ i, σ i → ℤ) :
    alignmentNativeJointArrayGroup n u hu ≃* alignmentNativeJointArrayGroup n u hu where
  toFun a i := alignmentNativeArrayTranslation (n i) (u i) (hu i) (v i) (a i)
  invFun a i := (alignmentNativeArrayTranslation (n i) (u i) (hu i) (v i)).symm (a i)
  left_inv a := funext (fun i => (alignmentNativeArrayTranslation (n i) (u i) (hu i) (v i)).symm_apply_apply (a i))
  right_inv a := funext (fun i => (alignmentNativeArrayTranslation (n i) (u i) (hu i) (v i)).apply_symm_apply (a i))
  map_mul' a b := funext (fun i => map_mul _ (a i) (b i))

theorem alignmentNativeJointArrayTranslation_lattice (Γ : ∀ i, Subgroup (G i))
    (v : ∀ i, σ i → ℤ) (a : alignmentNativeJointArrayGroup n u hu) :
    alignmentNativeJointArrayTranslation n u hu v a ∈ alignmentNativeJointArrayLattice n u hu Γ ↔
      a ∈ alignmentNativeJointArrayLattice n u hu Γ := by
  change (∀ i, i ∈ Set.univ → alignmentNativeArrayTranslation (n i) (u i) (hu i) (v i) (a i) ∈
    pointwiseArrayLattice _ (Γ i)) ↔ (∀ i, i ∈ Set.univ → a i ∈ pointwiseArrayLattice _ (Γ i))
  simp only [alignmentNativeArrayTranslation_lattice]

theorem alignmentNativeJointArrayTranslation_continuous (v : ∀ i, σ i → ℤ) :
    Continuous (alignmentNativeJointArrayTranslation n u hu v) :=
  continuous_pi (fun i => (alignmentNativeArrayTranslation_continuous (n i) (u i) (hu i) (v i)).comp
    (continuous_apply i))

noncomputable def alignmentNativeJointCosetTranslation (Γ : ∀ i, Subgroup (G i))
    (v : ∀ i, σ i → ℤ) :
    alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ →
      alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ :=
  Quotient.lift (fun a => QuotientGroup.mk (alignmentNativeJointArrayTranslation n u hu v a)) (by
    intro a b hab
    apply QuotientGroup.eq.mpr
    have h := (alignmentNativeJointArrayTranslation_lattice n u hu Γ v (a⁻¹ * b)).mpr
      (QuotientGroup.leftRel_apply.mp hab)
    simpa only [map_mul, map_inv] using h)

theorem alignmentNativeJointCosetTranslation_continuous (Γ : ∀ i, Subgroup (G i))
    (v : ∀ i, σ i → ℤ) : Continuous (alignmentNativeJointCosetTranslation n u hu Γ v) :=
  continuous_quot_lift _ (QuotientGroup.continuous_mk.comp
    (alignmentNativeJointArrayTranslation_continuous n u hu v))

theorem alignmentNativeJointCosetTranslation_evaluation (Γ : ∀ i, Subgroup (G i))
    (v : ∀ i, σ i → ℤ) (i : ι) (z : σ i → ℤ)
    (y : alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ) :
    alignmentNativeJointCosetEvaluation n u hu Γ i z (alignmentNativeJointCosetTranslation n u hu Γ v y) =
      alignmentNativeJointCosetEvaluation n u hu Γ i (z + v i) y := by
  induction y using Quotient.inductionOn with
  | _ a => rfl

theorem alignmentNativeJointModelArray_translation [∀ i, Fintype (σ i)]
    (g x : ∀ i, G i) (k : ι → ℤ) (Δ v : ∀ i, σ i → ℤ) :
    alignmentNativeJointArrayTranslation n u hu v (alignmentNativeJointModelArray n u hu g x k Δ) =
      alignmentNativeJointModelArray n u hu g x (fun i => k i + ∑ j, v i j * Δ i j) Δ := by
  funext i
  exact alignmentNativeModelArray_input_translation (n i) (u i) (hu i) (g i) (x i) (k i) (Δ i) (v i)

theorem alignmentNativeJointModelStep_translation (g : ∀ i, G i) (t : ι → ℤ)
    (v : ∀ i, σ i → ℤ) :
    alignmentNativeJointArrayTranslation n u hu v (alignmentNativeJointModelStep n u hu g t) =
      alignmentNativeJointModelStep n u hu g t := rfl

theorem alignmentNativeJointArrayTranslation_add (v w : ∀ i, σ i → ℤ)
    (a : alignmentNativeJointArrayGroup n u hu) :
    alignmentNativeJointArrayTranslation n u hu v (alignmentNativeJointArrayTranslation n u hu w a) =
      alignmentNativeJointArrayTranslation n u hu (v + w) a := by
  funext i
  exact alignmentNativeArrayTranslation_add (n i) (u i) (hu i) (v i) (w i) (a i)

theorem alignmentNativeJointCosetTranslation_add (Γ : ∀ i, Subgroup (G i))
    (v w : ∀ i, σ i → ℤ)
    (y : alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ) :
    alignmentNativeJointCosetTranslation n u hu Γ v (alignmentNativeJointCosetTranslation n u hu Γ w y) =
      alignmentNativeJointCosetTranslation n u hu Γ (v + w) y := by
  induction y using Quotient.inductionOn with
  | _ a => exact congrArg QuotientGroup.mk (alignmentNativeJointArrayTranslation_add n u hu v w a)

theorem alignmentNativeJointCosetTranslation_zero (Γ : ∀ i, Subgroup (G i))
    (y : alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ) :
    alignmentNativeJointCosetTranslation n u hu Γ 0 y = y := by
  induction y using Quotient.inductionOn with
  | _ a =>
    apply congrArg QuotientGroup.mk
    funext i
    apply Subtype.ext
    funext z
    change (a i).val (z + 0) = (a i).val z
    rw [add_zero]

noncomputable def alignmentNativeJointCosetTranslationHomeomorph (Γ : ∀ i, Subgroup (G i))
    (v : ∀ i, σ i → ℤ) :
    (alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ) ≃ₜ
      (alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ) where
  toFun := alignmentNativeJointCosetTranslation n u hu Γ v
  invFun := alignmentNativeJointCosetTranslation n u hu Γ (-v)
  left_inv y := by
    rw [alignmentNativeJointCosetTranslation_add, neg_add_cancel, alignmentNativeJointCosetTranslation_zero]
  right_inv y := by
    rw [alignmentNativeJointCosetTranslation_add, add_neg_cancel, alignmentNativeJointCosetTranslation_zero]
  continuous_toFun := alignmentNativeJointCosetTranslation_continuous n u hu Γ v
  continuous_invFun := alignmentNativeJointCosetTranslation_continuous n u hu Γ (-v)

theorem alignmentNativeJointModelCosetOrbit_translation [∀ i, Fintype (σ i)]
    (Γ : ∀ i, Subgroup (G i)) (g x : ∀ i, G i) (k t : ι → ℤ) (Δ v : ∀ i, σ i → ℤ) (ℓ : ℤ) :
    alignmentNativeJointCosetTranslation n u hu Γ v (alignmentNativeJointModelCosetOrbit n u hu Γ g x k t Δ ℓ) =
      alignmentNativeJointModelCosetOrbit n u hu Γ g x (fun i => k i + ∑ j, v i j * Δ i j) t Δ ℓ := by
  apply congrArg QuotientGroup.mk
  funext i
  have h := alignmentNativeModelArray_input_translation (n i) (u i) (hu i)
    (g i) (x i) (k i + t i * ℓ) (Δ i) (v i)
  have he : (k i + t i * ℓ) + ∑ j, v i j * Δ i j = (k i + ∑ j, v i j * Δ i j) + t i * ℓ := by ring
  rw [he] at h
  exact h

end Hindman168
