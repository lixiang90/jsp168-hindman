import Hindman168.AlignmentNativeModelCosetOrbit
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

noncomputable def alignmentNativeArrayReading (Γ : Subgroup G)
    (f : C(G ⧸ Γ, ℝ)) (z : σ → ℤ) :
    C(alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
      pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ, ℝ) :=
  f.comp ⟨alignmentNativeArrayCosetEvaluation n u hu Γ z,
    alignmentNativeArrayCosetEvaluation_continuous n u hu Γ z⟩

theorem alignmentNativeArrayReading_modelOrbit [Fintype σ] (Γ : Subgroup G)
    (f : C(G ⧸ Γ, ℝ)) (g x : G) (k t : ℤ) (Δ z : σ → ℤ) (ℓ : ℤ) :
    alignmentNativeArrayReading n u hu Γ f z
      (alignmentNativeModelCosetOrbit n u hu Γ g x k t Δ ℓ) =
      f ((g ^ (k + t * ℓ + ∑ j, z j * Δ j) * x : G ⧸ Γ)) := rfl

theorem alignmentNativeArrayReading_translation (Γ : Subgroup G)
    (f : C(G ⧸ Γ, ℝ)) (v z : σ → ℤ)
    (y : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
      pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) :
    alignmentNativeArrayReading n u hu Γ f z
      (alignmentNativeArrayCosetTranslation n u hu Γ v y) =
      alignmentNativeArrayReading n u hu Γ f (z + v) y := by
  change f (alignmentNativeArrayCosetEvaluation n u hu Γ z
    (alignmentNativeArrayCosetTranslation n u hu Γ v y)) = _
  rw [alignmentNativeArrayCosetTranslation_evaluation]
  rfl

theorem alignmentNativeArrayReading_bound (Γ : Subgroup G)
    (f : C(G ⧸ Γ, ℝ)) (B : ℝ) (hf : ∀ x, |f x| ≤ B) (z : σ → ℤ)
    (y : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
      pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) :
    |alignmentNativeArrayReading n u hu Γ f z y| ≤ B :=
  hf _

end Hindman168
