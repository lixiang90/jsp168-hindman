import Hindman168.AlignmentNativeFiniteLattice

namespace Hindman168
open scoped Manifold ContDiff

attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

variable {σ : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G]

/-! The logarithms of the actual all-integer lattice span the entire
finite evaluation image. This is not yet a cocompactness theorem. -/

theorem alignmentNativeFiniteLattice_logarithms_span (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (Γ : Subgroup G) [CompactSpace (G ⧸ Γ)] :
    letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
    Submodule.span ℝ
      ((nativeLieGlobalLogarithm (I := nativeFiniteProductCorners I n) (G := nativeFiniteProduct G n)) ''
        (alignmentNativeFiniteAmbientLattice n u hu Γ : Set (nativeFiniteProduct G n))) =
      nativeLieSubalgebraModel (E := nativeFiniteProduct E n)
        (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u).range := by
  letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
  let f := alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u
  let K := alignmentNativeFiniteAmbientLattice n u hu Γ
  let W := Submodule.span ℝ
    ((nativeLieGlobalLogarithm (I := nativeFiniteProductCorners I n) (G := nativeFiniteProduct G n)) ''
      (K : Set (nativeFiniteProduct G n)))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, rfl⟩
    exact (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff
      (E := nativeFiniteProduct E n) f.range g).mp
        (alignmentNativeFiniteAmbientLattice_le n u hu Γ hg)
  · have hle : (⊤ : Submodule ℝ (alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G))) ≤
        W.comap f.toLinearMap := by
      rw [← alignmentNativeAllIntegerLatticeCoefficients_span (σ := σ) (E := E) (I := I) Γ]
      apply Submodule.span_le.mpr
      intro x hx
      change f x ∈ W
      apply Submodule.subset_span
      refine ⟨nativeLieExponential (I := nativeFiniteProductCorners I n)
        (G := nativeFiniteProduct G n) (f x), ?_, ?_⟩
      · exact (alignmentNativeFiniteAmbientLattice_exponential_mem_iff n u hu Γ x).mpr hx
      · exact nativeLieGlobalLogarithm_exponential
          (I := nativeFiniteProductCorners I n) (G := nativeFiniteProduct G n) (f x)
    intro v hv
    obtain ⟨x, hx⟩ := (LieHom.mem_range f v).mp hv
    exact hx ▸ hle (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ _))

end Hindman168

