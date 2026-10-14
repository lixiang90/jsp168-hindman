import Hindman168.NativeCenterCompactRepresentatives
import Hindman168.NormalQuotientLatticeDiscreteness
import Hindman168.NormalQuotientLatticeCocompactness

/-! The image of the actual specified lattice in the original center
quotient is discrete and cocompact in the natural quotient topology.
No quotient lattice property is supplied as an extra hypothesis. -/

namespace Hindman168
open scoped Manifold ContDiff

theorem nativeLattice_center_quotient_image_cocompact
    {G : Type*} [Group G] [TopologicalSpace G] (Γ : Subgroup G)
    [CompactSpace (G ⧸ Γ)] :
    CompactSpace ((G ⧸ Subgroup.center G) ⧸ Γ.map (QuotientGroup.mk' (Subgroup.center G))) :=
  normalQuotient_lattice_image_cocompact Γ (Subgroup.center G)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
include I

theorem nativeLattice_center_quotient_image_discrete (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    DiscreteTopology (Γ.map (QuotientGroup.mk' (Subgroup.center G))) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  letI : LocallyCompactSpace G := nativeLieGroup_locallyCompact (E := E) (I := I) (G := G)
  letI : IsClosed (Subgroup.center G : Set G) := center_isClosed (G := G)
  obtain ⟨C, hC, hCN, hcover⟩ := nativeLattice_exists_compact_center_representatives (I := I) Γ
  exact normalQuotient_lattice_image_discrete Γ (Subgroup.center G) hC hCN hcover

end Hindman168
