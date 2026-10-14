import Hindman168.AlignmentNativeModelArrayMembership

namespace Hindman168
open scoped Manifold ContDiff BigOperators TensorProduct

attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

variable {σ : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G]

variable (n : ℕ) (u : Fin (n + 1) → σ → ℤ)
  (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))

noncomputable def alignmentNativeConstantArray (x : G) :
    alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu :=
  ⟨fun _ => x, alignmentNativeArrayGroup_constant n u hu x⟩

noncomputable def alignmentNativeModelArray [Fintype σ]
    (g x : G) (k : ℤ) (Δ : σ → ℤ) : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu :=
  ⟨fun z => g ^ (k + ∑ j, z j * Δ j) * x,
    alignmentNativeArrayGroup_model n u hu g x k Δ⟩

noncomputable def alignmentNativeModelOrbit [Fintype σ]
    (g x : G) (k t : ℤ) (Δ : σ → ℤ) (ℓ : ℤ) : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu :=
  alignmentNativeModelArray n u hu g x (k + t * ℓ) Δ

theorem alignmentNativeModelArray_evaluation [Fintype σ]
    (g x : G) (k : ℤ) (Δ z : σ → ℤ) :
    (fun a : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu => a.val z) (alignmentNativeModelArray n u hu g x k Δ) =
      g ^ (k + ∑ j, z j * Δ j) * x := rfl

theorem alignmentNativeModelArray_input_translation [Fintype σ]
    (g x : G) (k : ℤ) (Δ v : σ → ℤ) :
    alignmentNativeArrayTranslation n u hu v (alignmentNativeModelArray n u hu g x k Δ) =
      alignmentNativeModelArray n u hu g x (k + ∑ j, v j * Δ j) Δ := by
  apply Subtype.ext
  funext z
  change g ^ (k + ∑ j, (z + v) j * Δ j) * x =
    g ^ ((k + ∑ j, v j * Δ j) + ∑ j, z j * Δ j) * x
  have he : k + ∑ j, (z + v) j * Δ j =
      (k + ∑ j, v j * Δ j) + ∑ j, z j * Δ j := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  rw [he]

theorem alignmentNativeConstantArray_power_evaluation
    (g : G) (t ℓ : ℤ) (z : σ → ℤ) :
    (fun a : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu => a.val z) ((alignmentNativeConstantArray (σ := σ) n u hu (g ^ t)) ^ ℓ) =
      g ^ (t * ℓ) := by
  change (g ^ t) ^ ℓ = g ^ (t * ℓ)
  exact (zpow_mul g t ℓ).symm

theorem alignmentNativeModelOrbit_linear [Fintype σ]
    (g x : G) (k t : ℤ) (Δ : σ → ℤ) (ℓ : ℤ) :
    alignmentNativeModelOrbit n u hu g x k t Δ ℓ =
      alignmentNativeConstantArray n u hu (g ^ t) ^ ℓ * alignmentNativeModelArray n u hu g x k Δ := by
  apply Subtype.ext
  funext z
  change g ^ ((k + t * ℓ) + ∑ j, z j * Δ j) * x =
    (g ^ t) ^ ℓ * (g ^ (k + ∑ j, z j * Δ j) * x)
  rw [← zpow_mul, ← mul_assoc, ← zpow_add]
  congr 2
  ring


theorem alignmentNativeConstantArray_translation (g : G) (v : σ → ℤ) :
    alignmentNativeArrayTranslation n u hu v (alignmentNativeConstantArray n u hu g) =
      alignmentNativeConstantArray n u hu g := rfl

theorem alignmentNativeModelArray_unit_translation [Fintype σ] [DecidableEq σ]
    (g x : G) (k : ℤ) (Δ : σ → ℤ) (j : σ) :
    alignmentNativeArrayTranslation n u hu (Pi.single j 1) (alignmentNativeModelArray n u hu g x k Δ) =
      alignmentNativeModelArray n u hu g x (k + Δ j) Δ := by
  rw [alignmentNativeModelArray_input_translation]
  congr 1
  simp [Pi.single_apply]

end Hindman168

