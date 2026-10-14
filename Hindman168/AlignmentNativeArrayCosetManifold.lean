import Hindman168.NativeDiscreteCosetManifold
import Hindman168.AlignmentNativeArrayLieGroup
import Hindman168.AlignmentNativeArrayLattice
import Hindman168.AlignmentNativeArrayCosetTranslations

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

variable (n : ℕ) (u : Fin (n + 1) → σ → ℤ)
  (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))

variable (Γ : Subgroup G) [DiscreteTopology Γ]

@[reducible]
noncomputable def alignmentNativeArrayCosetChartedSpace :
    ChartedSpace (alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
      (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
        pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) := by
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  letI := alignmentNativeArray_lieGroup n u hu
  letI := alignmentNativeArrayLattice_discrete n u hu Γ
  letI : IsTopologicalGroup (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :=
    topologicalGroup_of_lieGroup 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u) ∞
  exact discreteCosetGlobalChartedSpace (alignmentNativeArrayExponentialDiffeomorph n u hu)
    (pointwiseArrayLattice _ Γ)

theorem alignmentNativeArrayCoset_isManifold :
    letI := alignmentNativeArrayCosetChartedSpace (E := E) (I := I) (G := G) n u hu Γ
    IsManifold 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u) ∞
      (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
        pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) := by
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  letI := alignmentNativeArray_lieGroup n u hu
  letI := alignmentNativeArrayLattice_discrete n u hu Γ
  letI : IsTopologicalGroup (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :=
    topologicalGroup_of_lieGroup 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u) ∞
  exact discreteCosetGlobal_isManifold (alignmentNativeArrayExponentialDiffeomorph n u hu)
    (pointwiseArrayLattice _ Γ)

theorem alignmentNativeArrayCosetEvaluation_contMDiff (z : σ → ℤ) :
    letI := alignmentNativeArrayCosetChartedSpace (E := E) (I := I) (G := G) n u hu Γ
    letI := nativeDiscreteCosetChartedSpace (E := E) (I := I) Γ
    ContMDiff 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u) 𝓘(ℝ, E) ∞
      (alignmentNativeArrayCosetEvaluation n u hu Γ z) := by
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  letI := alignmentNativeArray_lieGroup n u hu
  letI := alignmentNativeArrayLattice_discrete n u hu Γ
  letI : IsTopologicalGroup (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :=
    topologicalGroup_of_lieGroup 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u) ∞
  letI := nativeDiscreteCosetChartedSpace (E := E) (I := I) Γ
  apply discreteCoset_contMDiff_of_projection (alignmentNativeArrayExponentialDiffeomorph n u hu)
    (pointwiseArrayLattice _ Γ)
  exact (nativeDiscreteCoset_projection_contMDiff (E := E) (I := I) Γ).comp
    (alignmentNativeArray_evaluation_contMDiff n u hu z)

end Hindman168
