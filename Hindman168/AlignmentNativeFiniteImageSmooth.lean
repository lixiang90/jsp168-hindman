import Hindman168.AlignmentNativeArrayTopology
import Hindman168.NativeLieSubalgebraIntegrationSmooth

namespace Hindman168
open scoped Manifold ContDiff

attribute [local instance 10] nativeFiniteProductTopologicalSpace
attribute [local instance] nativeFiniteProductGroup
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

noncomputable abbrev alignmentNativeFiniteImageModel (n : ℕ) (u : Fin (n + 1) → σ → ℤ) :=
  nativeLieSubalgebraModel (E := nativeFiniteProduct E n)
    (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u).range

@[reducible]
noncomputable def alignmentNativeFiniteImageChartedSpace (n : ℕ) (u : Fin (n + 1) → σ → ℤ) :
    ChartedSpace (alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
      (alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u) := by
  letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
  exact nativeLieSubalgebraChartedSpace (E := nativeFiniteProduct E n)
    (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u).range

theorem alignmentNativeFiniteImage_lieGroup (n : ℕ) (u : Fin (n + 1) → σ → ℤ) :
    letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
    LieGroup 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u) ∞
      (alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u) := by
  letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
  exact nativeLieSubalgebra_lieGroup (E := nativeFiniteProduct E n)
    (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u).range

theorem alignmentNativeIntegerEvaluation_contMDiff (n : ℕ) (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (z : σ → ℤ) :
    letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
    ContMDiff 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u) I ∞
      (alignmentNativeIntegerEvaluation (E := E) (I := I) (G := G) n u hu z) := by
  letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
  exact nativeLieSubalgebraIntegrate_contMDiff (E := nativeFiniteProduct E n) (F := E)
    (I := nativeFiniteProductCorners I n) (J := I) (G := nativeFiniteProduct G n) (K := G)
    (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u).range _

noncomputable def alignmentNativeFiniteImageExponentialDiffeomorph (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ) :
    letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
    let J := 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
    Diffeomorph J J (alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
      (alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u) ∞ := by
  letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
  exact nativeLieSubalgebraExponentialDiffeomorph (E := nativeFiniteProduct E n)
    (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u).range

end Hindman168

