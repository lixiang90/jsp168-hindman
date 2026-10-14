import Hindman168.AlignmentNativeJointReadings
import Hindman168.FiniteObservablePullbackLimits
import Hindman168.AlignmentNativeModelCosetOrbit

namespace Hindman168
open Filter NNReal
open scoped Manifold ContDiff BigOperators Topology

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

theorem alignmentNativeJointReading_compact_family
    (Γ : ∀ i, Subgroup (G i)) (i : ι)
    (K : Set C(G i ⧸ Γ i, ℝ)) (hK : IsCompact K) :
    IsCompact ((fun f : C(G i ⧸ Γ i, ℝ) => fun z =>
      alignmentNativeJointReading n u hu Γ i f z) '' K) := by
  exact observable_pullback_family_compact
    (fun z => ⟨alignmentNativeJointCosetEvaluation n u hu Γ i z,
      alignmentNativeJointCosetEvaluation_continuous n u hu Γ i z⟩) K hK

theorem alignmentNativeJointReading_uniform_subsequence [Fintype ι]
    (Γ : ∀ i, Subgroup (G i)) [∀ i, CompactSpace (G i ⧸ Γ i)]
    (M : ∀ i, MetricSpace (G i ⧸ Γ i))
    (ht : ∀ i, (inferInstance : TopologicalSpace (G i ⧸ Γ i)) =
      (M i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (f : ℕ → ∀ i, C(G i ⧸ Γ i, ℝ)) (B : ι → ℝ) (L : ι → ℝ≥0)
    (hB : ∀ k i x, |f k i x| ≤ B i)
    (hL : ∀ k i x y, dist (f k i x) (f k i y) ≤
      (L i : ℝ) * @dist (G i ⧸ Γ i) (M i).toDist x y) :
    ∃ g : ∀ i, C(G i ⧸ Γ i, ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ i z y,
        |alignmentNativeJointReading n u hu Γ i (f (φ k) i) z y -
          alignmentNativeJointReading n u hu Γ i (g i) z y| < ε := by
  exact finite_compatibleMetric_pullback_subsequence M ht
    (fun i z => alignmentNativeJointCosetEvaluation n u hu Γ i z) f B L hB hL

end Hindman168
