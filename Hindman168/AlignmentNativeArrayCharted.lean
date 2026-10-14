import Hindman168.AlignmentNativeFiniteImageSmooth

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

noncomputable def alignmentNativeArrayExponentialHomeomorph (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u ≃ₜ
      alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu := by
  letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
  exact (alignmentNativeFiniteImageExponentialDiffeomorph (E := E) (I := I) (G := G) n u).toHomeomorph.trans
    (alignmentNativeArrayHomeomorph n u hu)

@[reducible]
noncomputable def alignmentNativeArrayChartedSpace (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    ChartedSpace (alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
      (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :=
  homeomorphSingletonChart (alignmentNativeArrayExponentialHomeomorph n u hu)

theorem alignmentNativeArray_isManifold (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
    IsManifold 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u) ∞
      (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :=
  homeomorphSingletonChart_isManifold (alignmentNativeArrayExponentialHomeomorph n u hu)

noncomputable def alignmentNativeArrayExponentialDiffeomorph (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
    let J := 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
    Diffeomorph J J (alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
      (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) ∞ :=
  homeomorphSingletonDiffeomorph (alignmentNativeArrayExponentialHomeomorph n u hu)

noncomputable def alignmentNativeArrayDiffeomorph (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
    letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
    let J := 𝓘(ℝ, alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u)
    Diffeomorph J J (alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u)
      (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) ∞ := by
  letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  exact (alignmentNativeFiniteImageExponentialDiffeomorph (E := E) (I := I) (G := G) n u).symm.trans
    (alignmentNativeArrayExponentialDiffeomorph n u hu)

theorem alignmentNativeArrayDiffeomorph_apply (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (g : alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u) :
    alignmentNativeArrayDiffeomorph n u hu g = alignmentNativeArrayEquiv n u hu g := by
  letI := alignmentNativeFiniteImageChartedSpace (E := E) (I := I) (G := G) n u
  let e := alignmentNativeFiniteImageExponentialDiffeomorph (E := E) (I := I) (G := G) n u
  exact congrArg (alignmentNativeArrayHomeomorph n u hu) (e.apply_symm_apply g)

end Hindman168

