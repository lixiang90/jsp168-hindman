import Hindman168.CenterCompactRepresentatives
import Hindman168.CocompactDiscreteSubgroupFiniteGeneration
import Hindman168.OpenMapCompactRepresentatives
import Mathlib.Topology.Constructions

/-! Genuine compactness of the natural center quotient by the actual
intersection lattice. A compact representative set is constructed from
the original compact coset quotient and the finite commutator records.
The restricted lattice keeps its natural subtype topology and is discrete. -/

namespace Hindman168
open Function Set
open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
 theorem compact_quotient_of_compact_representatives (Γ : Subgroup G)
    {C : Set G} (hC : IsCompact C) (hcover : C * (Γ : Set G) = univ) :
    CompactSpace (G ⧸ Γ) := by
  apply isCompact_univ_iff.mp
  have hq : (QuotientGroup.mk : G → G ⧸ Γ) '' C = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective (s := Γ) x
    have hg : g ∈ C * (Γ : Set G) := by rw [hcover]; trivial
    obtain ⟨c, hc, γ, hγ, he⟩ := mem_mul.mp hg
    refine ⟨c, hc, QuotientGroup.eq.mpr ?_⟩
    rw [← he, inv_mul_cancel_left]
    exact hγ
  rw [← hq]
  exact hC.image QuotientGroup.continuous_mk

variable [T2Space G]

omit [IsTopologicalGroup G] [T2Space G] in
 theorem discreteSubgroup_center_intersection_discrete (Γ : Subgroup G) [DiscreteTopology Γ] :
    DiscreteTopology (Γ.subgroupOf (Subgroup.center G)) := by
  let f : Γ.subgroupOf (Subgroup.center G) → Γ := fun γ => ⟨γ.val.val, γ.property⟩
  have hf : Continuous f := by fun_prop
  have hi : Injective f := by
    intro γ δ he
    exact Subtype.ext (Subtype.ext (congrArg (fun g : Γ => (g : G)) he))
  exact DiscreteTopology.of_continuous_injective hf hi

variable [LocallyCompactSpace G]

 theorem center_quotient_compactSpace_of_lattice_centralizer (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (hfg : Γ.FG)
    (hcentral : Subgroup.centralizer (Γ : Set G) = Subgroup.center G) :
    CompactSpace ((Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G)) := by
  obtain ⟨K, O, hK, _, hOK, hq⟩ := exists_compact_open_representatives
    (QuotientGroup.isOpenMap_coe (N := Γ)) (QuotientGroup.mk_surjective (s := Γ))
  have hcover : K * (Γ : Set G) = univ := by
    apply eq_univ_of_forall
    intro g
    have hg : g ∈ O * (Γ : Set G) := by
      rw [subgroup_open_representatives_mul_eq_univ Γ O hq]
      trivial
    exact (mul_subset_mul hOK subset_rfl) hg
  obtain ⟨D, hD, hcoverD⟩ := exists_compact_center_subtype_representatives Γ hfg hcentral hK hcover
  exact compact_quotient_of_compact_representatives (Γ.subgroupOf (Subgroup.center G)) hD hcoverD

end Hindman168
