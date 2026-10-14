import Hindman168.AlignmentNativeModelArrays
import Hindman168.AlignmentNativeArrayCosetTranslations

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

noncomputable def alignmentNativeModelCosetOrbit [Fintype σ] (Γ : Subgroup G)
    (g x : G) (k t : ℤ) (Δ : σ → ℤ) (ℓ : ℤ) :
    alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
      pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ :=
  QuotientGroup.mk (alignmentNativeModelOrbit n u hu g x k t Δ ℓ)

theorem alignmentNativeModelCosetOrbit_evaluation [Fintype σ] (Γ : Subgroup G)
    (g x : G) (k t : ℤ) (Δ z : σ → ℤ) (ℓ : ℤ) :
    alignmentNativeArrayCosetEvaluation n u hu Γ z (alignmentNativeModelCosetOrbit n u hu Γ g x k t Δ ℓ) =
      (g ^ (k + t * ℓ + ∑ j, z j * Δ j) * x : G ⧸ Γ) := rfl

theorem alignmentNativeModelCosetOrbit_linear [Fintype σ] (Γ : Subgroup G)
    (g x : G) (k t : ℤ) (Δ : σ → ℤ) (ℓ : ℤ) :
    alignmentNativeModelCosetOrbit n u hu Γ g x k t Δ ℓ =
      (alignmentNativeConstantArray n u hu (g ^ t) ^ ℓ) •
        (QuotientGroup.mk (alignmentNativeModelArray n u hu g x k Δ) :
          alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
          pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) := by
  unfold alignmentNativeModelCosetOrbit
  rw [alignmentNativeModelOrbit_linear]
  rfl

theorem alignmentNativeModelCosetOrbit_translation [Fintype σ] (Γ : Subgroup G)
    (g x : G) (k t : ℤ) (Δ v : σ → ℤ) (ℓ : ℤ) :
    alignmentNativeArrayCosetTranslation n u hu Γ v (alignmentNativeModelCosetOrbit n u hu Γ g x k t Δ ℓ) =
      alignmentNativeModelCosetOrbit n u hu Γ g x (k + ∑ j, v j * Δ j) t Δ ℓ := by
  change QuotientGroup.mk (alignmentNativeArrayTranslation n u hu v
    (alignmentNativeModelArray n u hu g x (k + t * ℓ) Δ)) = _
  rw [alignmentNativeModelArray_input_translation]
  have h : (k + t * ℓ) + ∑ j, v j * Δ j = (k + ∑ j, v j * Δ j) + t * ℓ := by ring
  rw [h]
  rfl

end Hindman168
