import Hindman168.AlignmentNativeArrayTranslationCoordinates

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

theorem alignmentNativeArrayTranslation_contMDiff (v : σ → ℤ) :
    letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
    let J := 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
    ContMDiff J J ∞ (alignmentNativeArrayTranslation n u hu v) := by
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  let e := alignmentNativeArrayExponentialDiffeomorph n u hu
  let f := (alignmentNativeArrayModelTranslation n u hu v).toContinuousLinearMap
  have h := e.contMDiff_toFun.comp (f.contDiff.contMDiff.comp e.contMDiff_invFun)
  exact h.congr (fun a => by
    have he := alignmentNativeArrayTranslation_exponential n u hu v (e.symm a)
    change alignmentNativeArrayTranslation n u hu v a = e (f (e.symm a))
    exact (congrArg (alignmentNativeArrayTranslation n u hu v) (e.apply_symm_apply a)).symm.trans he)

noncomputable def alignmentNativeArrayTranslationDiffeomorph (v : σ → ℤ) :
    letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
    let J := 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
    Diffeomorph J J
      (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu)
      (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) ∞ := by
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  exact
    { toEquiv := (alignmentNativeArrayTranslation n u hu v).toEquiv
      contMDiff_toFun := alignmentNativeArrayTranslation_contMDiff n u hu v
      contMDiff_invFun := alignmentNativeArrayTranslation_contMDiff n u hu (-v) }

theorem alignmentNativeArrayTranslationDiffeomorph_apply (v : σ → ℤ)
    (a : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :
    alignmentNativeArrayTranslationDiffeomorph n u hu v a =
      alignmentNativeArrayTranslation n u hu v a := rfl

end Hindman168
