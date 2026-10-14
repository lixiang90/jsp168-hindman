import Hindman168.AlignmentNativeJointReadings
import Hindman168.AlignmentNativeJointCosetSmooth
import Hindman168.AlignmentNativeModelCosetOrbit

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

theorem alignmentNativeJointReading_contMDiff [Fintype ι]
    (Γ : ∀ i, Subgroup (G i)) [∀ i, DiscreteTopology (Γ i)]
    (i : ι) (f : C(G i ⧸ Γ i, ℝ)) (z : σ i → ℤ)
    (hf : letI := nativeDiscreteCosetChartedSpace (E := E i) (I := I i) (Γ i)
      ContMDiff 𝓘(ℝ, E i) 𝓘(ℝ, ℝ) ∞ f) :
    letI := alignmentNativeJointCosetChartedSpace n u hu Γ
    ContMDiff 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u)
      𝓘(ℝ, ℝ) ∞ (alignmentNativeJointReading n u hu Γ i f z) := by
  letI := alignmentNativeJointCosetChartedSpace n u hu Γ
  letI := nativeDiscreteCosetChartedSpace (E := E i) (I := I i) (Γ i)
  exact hf.comp (alignmentNativeJointCosetEvaluation_contMDiff n u hu Γ i z)

end Hindman168
