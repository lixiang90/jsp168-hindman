import Hindman168.OpenMapCompactRepresentatives
import Hindman168.DiscreteSubgroupCompactIntersection
import Hindman168.ConnectedSubgroupOverlapGeneration
import Mathlib.Topology.Algebra.Group.Quotient

/-! Any actual discrete cocompact subgroup of a locally compact
preconnected Hausdorff topological group is finitely generated. The finite
generators are the actual subgroup elements in K^-1*K for compact original
representatives; no finite-generation hypothesis is added. -/

namespace Hindman168
open Function Set
open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G]

omit [TopologicalSpace G] in
 theorem subgroup_open_representatives_mul_eq_univ (Γ : Subgroup G) (O : Set G)
    (h : (QuotientGroup.mk : G → G ⧸ Γ) '' O = univ) : O * (Γ : Set G) = univ := by
  apply eq_univ_of_forall
  intro g
  have hg : (QuotientGroup.mk g : G ⧸ Γ) ∈ (QuotientGroup.mk : G → G ⧸ Γ) '' O := by
    rw [h]
    trivial
  obtain ⟨o, ho, he⟩ := hg
  have hm : o⁻¹ * g ∈ Γ := (QuotientGroup.eq).mp he
  exact mem_mul.mpr ⟨o, ho, o⁻¹ * g, hm, mul_inv_cancel_left o g⟩

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [PreconnectedSpace G]

 theorem discreteCocompactSubgroup_fg (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] : Γ.FG := by
  obtain ⟨K, O, hK, hO, hOK, hq⟩ := exists_compact_open_representatives
    (QuotientGroup.isOpenMap_coe (N := Γ)) (QuotientGroup.mk_surjective (s := Γ))
  apply Γ.fg_iff.mpr
  refine ⟨{g : G | g ∈ Γ ∧ g ∈ K⁻¹ * K}, ?_, ?_⟩
  · exact subgroup_eq_closure_overlaps_of_open_cover Γ hO hOK
      (subgroup_open_representatives_mul_eq_univ Γ O hq)
  · exact discreteSubgroup_compact_inter_finite Γ (hK.inv.mul hK)

end Hindman168
