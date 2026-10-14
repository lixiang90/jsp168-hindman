import Hindman168.AlignmentNativeFiniteLatticeCompact
import Hindman168.SubgroupQuotientImageMap

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

/-! Cocompactness of the actual all-integer pointwise lattice in the
actual native exponential array group, with its inherited topology. -/

theorem alignmentNativeArrayLattice_quotient_compact (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    CompactSpace (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
      pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) := by
  letI := alignmentNativeFiniteLattice_quotient_compact n u hu Γ
  let e := alignmentNativeArrayEquiv (E := E) (I := I) (G := G) n u hu
  have h := subgroupQuotientImageMap_compactSpace e.toMonoidHom
    (alignmentNativeFiniteLattice n u hu Γ) (alignmentNativeArrayHomeomorph n u hu).continuous
    e.surjective
  have he : (alignmentNativeFiniteLattice n u hu Γ).map e.toMonoidHom =
      pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective _
  rw [he] at h
  exact h

theorem alignmentNativeCompactArray_exists [Finite σ]
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ (n : ℕ) (u : Fin (n + 1) → σ → ℤ)
      (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)),
      SimplyConnectedSpace (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) ∧
      DiscreteTopology (pointwiseArrayLattice
        (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) ∧
      CompactSpace (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu ⧸
        pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) := by
  obtain ⟨n, u, hu⟩ := alignmentNativeFiniteEvaluation_exists_injective (σ := σ) (E := E) (I := I) (G := G)
  exact ⟨n, u, hu, alignmentNativeArrayGroup_simplyConnected n u hu,
    alignmentNativeArrayLattice_discrete n u hu Γ,
    alignmentNativeArrayLattice_quotient_compact n u hu Γ⟩

end Hindman168

