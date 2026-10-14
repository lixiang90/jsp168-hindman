import Hindman168.AlignmentNativeFiniteLatticeSpan
import Hindman168.NativeFiniteProductLattice
import Hindman168.NativeRootSubgroupCompact

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

omit [Module ℚ E] in
theorem alignmentNativeFiniteAmbientLattice_le_product (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (Γ : Subgroup G) :
    alignmentNativeFiniteAmbientLattice n u hu Γ ≤ nativeFiniteProductLattice Γ n := by
  rintro g ⟨a, ha, rfl⟩
  apply (nativeFiniteProductLattice_mem_iff Γ n a.val).mpr
  intro i
  rw [← alignmentNativeIntegerEvaluation_selected n u hu a i]
  exact (alignmentNativeFiniteLattice_mem n u hu Γ a).mp ha (u i)

theorem alignmentNativeFiniteLattice_quotient_compact (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    CompactSpace (alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u ⧸
      alignmentNativeFiniteLattice n u hu Γ) := by
  letI := nativeFiniteProductSimplyConnected (I := I) (G := G) n
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I (minSmoothness ℝ 3)
  letI := nativeFiniteProductLattice_discrete Γ n
  letI := nativeFiniteProductLattice_cocompact Γ n
  letI : Module ℚ (nativeFiniteProduct E n) := Module.compHom _ (Rat.castHom ℝ)
  have h := nativeSpanningSubgroup_quotient_compact
    (E := nativeFiniteProduct E n) (I := nativeFiniteProductCorners I n)
    (nativeFiniteProductLattice Γ n) (alignmentNativeFiniteAmbientLattice n u hu Γ)
    (alignmentNativeFiniteAmbientLattice_le_product n u hu Γ)
    (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u).range
    (alignmentNativeFiniteLattice_logarithms_span n u hu Γ)
  have he : (alignmentNativeFiniteAmbientLattice n u hu Γ).comap
      (alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u).subtype =
        alignmentNativeFiniteLattice n u hu Γ :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  change CompactSpace (alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u ⧸
    (alignmentNativeFiniteAmbientLattice n u hu Γ).comap
      (alignmentNativeFiniteImageSubgroup (E := E) (I := I) (G := G) n u).subtype) at h
  rw [he] at h
  exact h

end Hindman168

