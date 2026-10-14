import Hindman168.NativeCenterLattice

/-! Compact representatives for the actual original center modulo the
intersection with the specified original lattice. All hypotheses of the
general compact-representative construction are derived here. -/

namespace Hindman168
open Set
open scoped Manifold ContDiff Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
include I

theorem nativeLattice_exists_compact_center_representatives (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ C : Set G, IsCompact C ∧ C ⊆ Subgroup.center G ∧
      (Subgroup.center G : Set G) ⊆ C * (Γ ⊓ Subgroup.center G : Subgroup G) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  letI : LocallyCompactSpace G := nativeLieGroup_locallyCompact (E := E) (I := I) (G := G)
  obtain ⟨K, O, hK, _, hOK, hq⟩ := exists_compact_open_representatives
    (QuotientGroup.isOpenMap_coe (N := Γ)) (QuotientGroup.mk_surjective (s := Γ))
  have hcover : K * (Γ : Set G) = univ := by
    apply eq_univ_of_forall
    intro g
    have hg : g ∈ O * (Γ : Set G) := by
      rw [subgroup_open_representatives_mul_eq_univ Γ O hq]
      trivial
    exact (mul_subset_mul hOK subset_rfl) hg
  exact exists_compact_center_representatives Γ (nativeLattice_fg (E := E) (I := I) Γ)
    (nativeLattice_centralizer_eq_center (E := E) (I := I) Γ) hK hcover

end Hindman168
