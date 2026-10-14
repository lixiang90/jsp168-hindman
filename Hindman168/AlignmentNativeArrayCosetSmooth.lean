import Hindman168.AlignmentNativeArrayCosetManifold
import Hindman168.AlignmentNativeArrayTranslationSmooth

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

theorem alignmentNativeArrayCosetProjection_contMDiff :
    letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
    letI := alignmentNativeArrayCosetChartedSpace (E := E) (I := I) (G := G) n u hu Γ
    let J := 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
    ContMDiff J J ∞ (QuotientGroup.mk (s := pointwiseArrayLattice
      (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ)) := by
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  letI := alignmentNativeArray_lieGroup n u hu
  letI := alignmentNativeArrayLattice_discrete n u hu Γ
  letI : IsTopologicalGroup (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :=
    topologicalGroup_of_lieGroup 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u) ∞
  exact discreteCosetProjection_contMDiff (alignmentNativeArrayExponentialDiffeomorph n u hu)
    (pointwiseArrayLattice _ Γ)

theorem alignmentNativeArrayCosetTranslation_contMDiff (v : σ → ℤ) :
    letI := alignmentNativeArrayCosetChartedSpace (E := E) (I := I) (G := G) n u hu Γ
    let J := 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
    ContMDiff J J ∞ (alignmentNativeArrayCosetTranslation n u hu Γ v) := by
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  letI := alignmentNativeArray_lieGroup n u hu
  letI := alignmentNativeArrayLattice_discrete n u hu Γ
  letI : IsTopologicalGroup (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :=
    topologicalGroup_of_lieGroup 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u) ∞
  letI := alignmentNativeArrayCosetChartedSpace (E := E) (I := I) (G := G) n u hu Γ
  apply discreteCoset_contMDiff_of_projection (alignmentNativeArrayExponentialDiffeomorph n u hu)
    (pointwiseArrayLattice _ Γ)
  exact (alignmentNativeArrayCosetProjection_contMDiff n u hu Γ).comp
    (alignmentNativeArrayTranslation_contMDiff n u hu v)

noncomputable def alignmentNativeArrayCosetTranslationDiffeomorph (v : σ → ℤ) :
    letI := alignmentNativeArrayCosetChartedSpace (E := E) (I := I) (G := G) n u hu Γ
    let J := 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
    let Q := alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
      pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ
    Diffeomorph J J Q Q ∞ := by
  letI := alignmentNativeArrayCosetChartedSpace (E := E) (I := I) (G := G) n u hu Γ
  exact
    { toEquiv := (alignmentNativeArrayCosetTranslationHomeomorph n u hu Γ v).toEquiv
      contMDiff_toFun := alignmentNativeArrayCosetTranslation_contMDiff n u hu Γ v
      contMDiff_invFun := alignmentNativeArrayCosetTranslation_contMDiff n u hu Γ (-v) }

theorem alignmentNativeArrayCosetTranslationDiffeomorph_apply (v : σ → ℤ)
    (y : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
      pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) :
    alignmentNativeArrayCosetTranslationDiffeomorph n u hu Γ v y =
      alignmentNativeArrayCosetTranslation n u hu Γ v y := rfl

end Hindman168
