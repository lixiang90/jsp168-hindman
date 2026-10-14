import Hindman168.NormalQuotientFiniteLatticeImage
import Hindman168.SubgroupFiniteIdentityNeighborhood
import Mathlib.Topology.Compactness.LocallyCompact

/-! Original lattice discreteness descends through an actual closed
normal subgroup when its specified intersection has actual compact
representatives. The proof uses a genuine original compact identity
neighborhood and the preceding finite actual quotient-image theorem. -/

namespace Hindman168
open Set Topology
open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

 theorem normalQuotient_lattice_image_discrete (Γ N : Subgroup G) [N.Normal]
    [DiscreteTopology Γ] [IsClosed (N : Set G)] {C : Set G}
    (hC : IsCompact C) (hCN : C ⊆ N)
    (hcover : (N : Set G) ⊆ C * (Γ ⊓ N : Subgroup G)) :
    DiscreteTopology (Γ.map (QuotientGroup.mk' N)) := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  apply subgroup_discrete_of_finite_identity_neighborhood
    (Γ.map (QuotientGroup.mk' N))
    ((QuotientGroup.isOpenMap_coe (N := N)) _ isOpen_interior)
  · exact ⟨1, mem_interior_iff_mem_nhds.mpr hK1, rfl⟩
  · exact normalQuotient_lattice_image_inter_finite Γ N hC hCN hcover hK interior_subset

end Hindman168
